"""Graviton absorption by a ring of atoms, with the same greybody spectrum for Bondi loss."""
from functools import lru_cache
from math import comb, factorial
from pathlib import Path
import json

import numpy as np
from scipy import constants
from scipy.integrate import quad, simpson, solve_ivp
from scipy.linalg import expm
from scipy.optimize import brentq, minimize
from scipy.special import eval_jacobi, factorial2

ROOT = Path(__file__).resolve().parents[1]
FREQUENCIES = (.015, .08, .16, .28, .40, .55, .70)


def jost_wave(omega, outer, ell, even, order):
    """Outgoing large-radius solution and its tortoise derivative, M=1."""
    angular = ell * (ell + 1)
    lam = (angular - 2) / 2
    if even:
        numerator = {2: 2*(lam+1), 3: 6., 4: 18/lam, 5: 18/lam**2}
        powers = {k: sum(val*(-3/lam)**(k-p)*(k-p+1) for p,val in numerator.items() if p<=k)
                  for k in range(2,order+2)}
    else:
        powers = {2: angular, 3: -6.}
    terms = [np.ones(len(ell),dtype=complex)]
    for n in range(1,order+1):
        a = (n-1)*n*terms[n-1]
        if n>=2:
            a = a-2*(n-2)*n*terms[n-2]
        for power, coefficient in powers.items():
            if power<=n+1:
                a = a-coefficient*terms[n+1-power]
        terms.append(a/(2j*omega*n))
    inv_r = 1/outer
    series = sum(v*inv_r**n for n,v in enumerate(terms))
    deriv = sum(-n*v*inv_r**(n+1) for n,v in enumerate(terms))
    phase = np.exp(1j*omega*(outer+2*np.log(outer/2-1)))
    return phase*np.stack([series,1j*omega*series+(1-2*inv_r)*deriv])


@lru_cache(None)
def transmission(omega, maximum=8, even=False):
    """Positive transmitted flux from a Wronskian, including probabilities far below machine epsilon."""
    ell = np.arange(2,maximum+1)
    angular = ell*(ell+1)
    lam = (angular-2)/2
    initial_y = -32. if not even else -36.
    outer = max(65.,(32+maximum*(maximum+1)*.50)/omega)
    tolerance = 2e-9 if not even else 4e-11
    def rhs(y, flat):
        radial_offset = np.exp(y)
        r = 2*(1+radial_offset)
        lapse = radial_offset/(1+radial_offset)
        base = angular/r**2-6/r**3
        if even:
            base = (2*lam**2*(lam+1)*r**3+6*lam**2*r*r+18*lam*r+18)/(r**3*(lam*r+3)**2)
        a, b = flat.reshape(2,-1)
        return np.concatenate([r*b,r*(lapse*base-omega**2)*a])
    def propagate(y0,y1,state):
        sol=solve_ivp(rhs,(y0,y1),state.ravel(),rtol=tolerance,atol=tolerance/100,method='DOP853')
        if not sol.success:
            raise ArithmeticError(sol.message)
        return sol.y[:,-1].reshape(2,-1)
    horizon_phase = np.exp(-1j*omega*(2*(1+np.exp(initial_y))+2*initial_y))
    infall = horizon_phase*np.array([np.ones(len(ell)),np.full(len(ell),-1j*omega)])
    outward = jost_wave(omega,outer,ell,even,18 if even else 14)
    outer_y = np.log(outer/2-1)
    if even:
        midpoint = np.log(3.)
        infall=propagate(initial_y,midpoint,infall)
        outward=propagate(outer_y,midpoint,outward)
    else:
        infall=propagate(initial_y,outer_y,infall)
    wronskian=infall[0]*outward[1]-infall[1]*outward[0]
    incoming=wronskian/(2j*omega)
    tau=1/abs(incoming)**2
    if not even:
        reflected=(outward[0].conj()*infall[1]-outward[1].conj()*infall[0])/(2j*omega)
        assert max(abs((abs(reflected)**2+1)/abs(incoming)**2-1))<2e-7
    assert np.all((tau>0)&(tau<1.0000002))
    return tau


def low_frequency(omega,ell):
    horizon_value=factorial(ell-2)*factorial(ell+2)/factorial(2*ell)
    return 4*(horizon_value/factorial2(2*ell+1))**2*(2*omega)**(2*ell+2)


@lru_cache(None)
def angular_weights(ell,latitude=0.):
    """Spin two in the local radial frame, expanded in the common axial basis."""
    m=np.arange(-ell,ell+1)
    raising=np.diag(np.sqrt((ell-m[:-1])*(ell+m[:-1]+1)),-1)
    angular_y=(raising-raising.T)/(2j)
    rotated=expm(-1j*(np.pi/2-latitude)*angular_y)[:,ell+2]
    weights=abs(rotated)**2
    assert abs(sum(weights)-1)<4e-15
    return m, weights


def ring_spectrum(tau,n,latitude=0.):
    ell=np.arange(2,len(tau)+2)
    flux=(2*ell+1)*tau
    g=np.zeros(n)
    for degree,weight in zip(ell,flux/sum(flux)):
        m,prob=angular_weights(int(degree),latitude)
        np.add.at(g,m%n,n*weight*prob)
    if latitude==0:
        angle=2*np.pi*np.arange(n)/n
        correlation=sum(f*np.cos(angle/2)**4*eval_jacobi(l-2,0,4,np.cos(angle))
                        for l,f in zip(ell,flux))/sum(flux)
        alternate=np.fft.fft(correlation)
        assert max(abs(alternate-g))<3e-13
    assert abs(sum(g)-n)<4e-13
    return g


def best_reliable_guess(g,marked):
    """Maximum joint probability of a correct conclusive mark, at fixed conclusive fraction."""
    n=len(g)
    if marked==1.:
        kept=g.copy()
    else:
        level=brentq(lambda a:np.minimum(a,g).sum()/n-marked,0.,float(max(g)))
        kept=np.minimum(level,g)
    right=(np.sqrt(kept).sum()/n)**2
    return right,kept


def check_instrument(g,marked):
    n=len(g)
    idx=np.arange(n)
    fourier=np.exp(2j*np.pi*idx[:,None]*idx[None,:]/n)/np.sqrt(n)
    amplitudes=fourier*np.sqrt(g)[:,None]
    right,kept=best_reliable_guess(g,marked)
    seed=np.sqrt(kept/g)
    operators=seed[:,None]*fourier
    probabilities=abs(operators.conj().T@amplitudes)**2/n
    assert abs(np.trace(probabilities)-right)<2e-12
    assert abs(np.sum(probabilities)-marked)<2e-12
    # Independently optimize the concave objective over the retained diagonal in the Fourier basis.
    if min(g)>1e-6 and marked not in (1.,min(g)) and marked>.01:
        objective=lambda x:-np.sqrt(np.maximum(x,1e-25)).sum()
        solution=minimize(objective,marked*g,bounds=[(0.,r) for r in g],
                          constraints=[dict(type='eq',fun=lambda x:x.sum()-n*marked)],
                          method='SLSQP', options=dict(ftol=1e-11,maxiter=300))
        assert solution.success and abs((-solution.fun/n)**2-right)<5e-9
    return right


def triangle(tau):
    """The invariant triple phase on a spherical triangle, versus its spin holonomy."""
    phi=2*np.pi*np.arange(3)/3
    theta=.72
    dirs=np.array([[np.sin(theta)*np.cos(a),np.sin(theta)*np.sin(a),np.cos(theta)] for a in phi])
    solid_angle=2*np.arctan2(np.linalg.det(dirs),1+sum(dirs[i]@dirs[(i+1)%3] for i in range(3)))
    ell=np.arange(2,len(tau)+2)
    weight=(2*ell+1)*tau
    # Spin transport in the same meridian frames as the general ring.
    lag=0j
    for l,w in zip(ell,weight/weight.sum()):
        m,prob=angular_weights(int(l),np.pi/2-theta)
        lag+=w*np.dot(prob,np.exp(2j*np.pi*m/3))
    predicted_lag=abs(sum(w*np.cos(np.arccos(dirs[0]@dirs[1])/2)**4*
                          eval_jacobi(l-2,0,4,dirs[0]@dirs[1]) for l,w in zip(ell,weight))/sum(weight))
    assert abs(abs(lag)-predicted_lag)<2e-14
    # Positive spin convention here yields minus twice the geometric solid angle.
    phase=np.angle(lag**3)
    assert abs(np.exp(1j*phase)-np.exp(-2j*solid_angle))<2e-12
    exact=ring_spectrum(tau,3,latitude=np.pi/2-theta)
    from_phase=np.array([1+2*abs(lag)*np.cos((phase+2*np.pi*q)/3) for q in range(3)])
    np.testing.assert_allclose(np.sort(from_phase),np.sort(exact),rtol=1e-13,atol=1e-13)
    return dict(colatitude=theta,solid_angle=solid_angle,closure=phase,
                pair_overlap=abs(lag),individual_fraction=min(exact))


def positronium():
    """Equal-mass constituents in the leading Coulomb and mass-quadrupole approximation (SI)."""
    mu=constants.m_e/2
    alpha,c,G,hbar=constants.alpha,constants.c,constants.G,constants.hbar
    radius=hbar/(mu*c*alpha)
    gap=(4/9)*mu*(c*alpha)**2/hbar
    vacuum=alpha**6*G*mu**3*c/(360*hbar**2)
    radial=quad(lambda r:8*r**6*np.exp(-4*r/3)/(81*np.sqrt(30)),0,np.inf,epsabs=2e-13)[0]
    # The full STF tensor contraction for one m has norm² 2/15 times the radial square.
    quad_norm=2*(mu*radius**2*radial)**2/15
    independent=2*G*gap**5*quad_norm/(5*hbar*c**5)
    assert abs(independent/vacuum-1)<1e-12
    return dict(omega=gap,gap_eV=hbar*gap/constants.e,spontaneous_s=vacuum)


def rates(omega,tau,atom,rho=100000.):
    gap=atom['omega']; redshift=np.sqrt(1-2/rho)
    mass_seconds=omega/(gap*redshift)
    distance_s=rho*mass_seconds
    flux=np.dot(2*np.arange(2,len(tau)+2)+1,tau)/np.expm1(8*np.pi*omega)
    gamma=5*atom['spontaneous_s']*flux/(8*(gap*distance_s)**2)
    return dict(radius_over_M=rho,mass_kg=mass_seconds*constants.c**3/constants.G,
                radius_m=distance_s*constants.c,upward_s=gamma,
                probability_before_annihilation=gamma*125.e-12)


def local_write_estimator(tau,h):
    """Calibrated six-mode data, eliminating the quadrupole and octupole contributions exactly."""
    g=ring_spectrum(tau,6)
    observed=h+(1-h)*g
    estimate=(4*observed[0]+8*observed[3]-9)/3
    baseline=(4*g[0]+8*g[3]-9)/3
    recovered=(estimate-baseline)/(1-baseline)
    weights=(2*np.arange(2,len(tau)+2)+1)*tau
    tail=weights[2:].sum()/weights.sum()
    assert abs(estimate-h)<=13*(1-h)*tail+2e-14
    assert abs(recovered-h)<3e-13
    per_event_variance=64*observed[0]/6+256*observed[3]/6-(estimate+3)**2
    return dict(input_fraction=h,uncorrected=estimate,calibrated=recovered,
                tail_fraction=tail,variance=per_event_variance)


def multiple_absorption(tau,n,k):
    """One coherent final temporal mode at each station. Select k locally excited atoms."""
    one=ring_spectrum(tau,n)/n
    distribution=np.zeros(n)
    distribution[0]=1.
    for _ in range(k):
        distribution=sum(one[j]*np.roll(distribution,j) for j in range(n))
    kernel=np.fft.ifft(n*one)
    independent=np.fft.fft(kernel**k)
    np.testing.assert_allclose(n*distribution,independent,atol=5e-14)
    return dict(atoms=k,minimum=n*min(distribution),dark_probability=min(distribution),
                dark_sector=int(np.argmin(distribution)),
                all_guess=float(np.sqrt(n*distribution).sum()/n)**2)


def tagged_site(tau,n):
    """Only the designated site may write. All other sites may abstain."""
    g=ring_spectrum(tau,n)
    # Scaling by the smallest eigenvalue keeps the reciprocal weights well conditioned.
    relative=g.min()/g
    cap=n*g.min()/relative.sum()
    norm_sq=n*(relative@relative)/relative.sum()**2
    assert 1-1e-13<=norm_sq<=n+1e-13 and cap<=n*min(g)
    # Local amplitude is one. The test vector minimizes the ordinary expectation.
    transform=np.exp(2j*np.pi*np.outer(np.arange(n),np.arange(n))/n)/np.sqrt(n)
    witness=transform@(np.sqrt(n)*relative/relative.sum())
    assert abs(witness[0]-1)<2e-14 and abs(np.vdot(witness,witness).real-norm_sq)<2e-13
    energy=np.sum(g*abs(transform.conj().T@witness)**2)
    assert abs(energy/cap-1)<3e-10
    if cap>1e-8:
        # Independent test in the site basis, including loss of positivity just beyond the boundary.
        G=(transform*g)@transform.conj().T
        e=np.zeros(n);e[0]=1
        direct=1/np.linalg.solve(G,e)[0].real
        assert abs(direct/cap-1)<2e-7
        G[0,0]-=cap
        assert abs(np.linalg.eigvalsh(G)[0])<8e-15
        G[0,0]-=.001*cap
        assert np.linalg.eigvalsh(G)[0]<0
    return dict(sites=n,maximum_local_mark=cap,witness_norm_squared=norm_sq,
                allowed_error_coefficient=n*norm_sq)


def opposite_hemisphere(tau):
    """All five auxiliary positions stay at least a right angle from the tagged station."""
    angles=np.pi*np.array([0.,.5,.75,1.,-.75,-.5])
    a=-(1+np.sqrt(2.))
    explicit=np.array([1.,a,-2*a,2*a-1,-2*a,a])
    angular_momentum=np.arange(2,len(tau)+2)
    flux=(2*angular_momentum+1)*tau
    rows=[]
    for ell,weight in zip(angular_momentum,flux/flux.sum()):
        m,prob=angular_weights(int(ell))
        waves=np.exp(1j*m[:,None]*angles[None,:])
        if ell==2:
            assert np.max(abs(waves@explicit))<6e-14
        if ell==3:
            np.testing.assert_allclose(abs((waves@explicit)[[0,-1]]),8+4*np.sqrt(2.),rtol=3e-15)
        rows.append(np.sqrt(weight*prob)[:,None]*waves)
    modes=np.vstack(rows)
    rest=np.linalg.lstsq(modes[:,1:],-modes[:,0],rcond=None)[0]
    optimal=np.concatenate(([1.],rest))
    cap=float(np.linalg.norm(modes@optimal)**2)
    witness_bound=float(np.linalg.norm(modes@explicit)**2)
    assert 0<cap<=witness_bound+2e-14
    assert np.linalg.norm(modes[:,1:].conj().T@(modes@optimal))<3e-13
    return dict(maximum_local_mark=cap,quadrupole_cancelled_bound=witness_bound,
                witness_norm_squared=float(np.vdot(optimal,optimal).real))


def recover_geometry(atom):
    """Invert one locally calibrated frequency and two measured collective populations."""
    x0, h0, radius_over_mass=.48,.23,100000.
    tau=transmission(x0)
    total=rates(x0,tau,atom,radius_over_mass)
    y=h0+(1-h0)*ring_spectrum(tau,6)
    reference=(1-y[3])/(y[0]-1)
    def ratio(x):
        g=ring_spectrum(transmission(float(x)),6)
        return (1-g[3])/(g[0]-1)
    trials=np.linspace(.45,.51,9)
    values=np.array([ratio(t) for t in trials])
    assert np.all(np.diff(values)>0) or np.all(np.diff(values)<0)
    fit=brentq(lambda x:ratio(x)-reference,trials[0],trials[-1],xtol=1e-12)
    t=transmission(fit);g=ring_spectrum(t,6)
    write=(y[3]-g[3])/(1-g[3])
    brightness=np.dot(2*np.arange(2,len(t)+2)+1,t)/np.expm1(8*np.pi*fit)
    light_distance=np.sqrt(5*atom['spontaneous_s']*brightness/(8*total['upward_s']))/atom['omega']
    scaled=fit/(atom['omega']*light_distance)
    compact=brentq(lambda v:v*np.sqrt(1-2*v)-scaled,0.,1/3,xtol=1e-18)
    mass=light_distance*compact*constants.c**3/constants.G
    assert abs(fit-x0)<3e-11 and abs(write-h0)<1e-11
    assert abs(mass/total['mass_kg']-1)<5e-10 and abs(compact*radius_over_mass-1)<3e-10
    return dict(Momega=fit,added_mark=write,R_m=light_distance*constants.c,M_kg=mass,
                compactness=compact,ratio=reference,ratio_slope=(ratio(x0+.0001)-ratio(x0-.0001))/.0002,
                search_bracket=trials[[0,-1]].tolist())


def mass_loss():
    """Integrate the positive spin-two Hawking energy flux over both helicities."""
    # The Boltzmann tail above x=1.44 is tiny. The first node is the exact zero-flux endpoint.
    xs=np.linspace(0.,1.44,145)
    ell=np.arange(2,9)
    partial=[np.zeros(len(ell))]
    for x in xs[1:]:
        tau=transmission(float(x))
        partial.append((2*ell+1)*x*tau/(np.pi*np.expm1(8*np.pi*x)))
    partial=np.array(partial)
    fine=simpson(partial,x=xs,axis=0); coarse=simpson(partial[::2],x=xs[::2],axis=0)
    assert abs(sum(fine)-sum(coarse))<2e-9,(sum(fine),sum(coarse))
    return dict(total=float(sum(fine)),ell2_fraction=fine[0]/sum(fine),
                partials=list(fine),coarser=float(sum(coarse)))


def main():
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    atom=positronium(); rows=[]
    for x in FREQUENCIES:
        tau=transmission(x)
        independent=transmission(x,maximum=8,even=True)
        assert max(abs(tau-independent)/np.maximum(tau,1e-65))<1.5e-6
        row=dict(Momega=x,transmission=list(tau),rates=rates(x,tau,atom),rings=[],
                 estimator=local_write_estimator(tau,.25),
                 designated_sites=[tagged_site(tau,n) for n in (5,6,8)],
                 opposite_hemisphere=opposite_hemisphere(tau),
                 six_station_blocks=[multiple_absorption(tau,6,k) for k in (1,2,3)])
        for n in (5,6,8):
            g=ring_spectrum(tau,n)
            small=float(min(g)); full,_=best_reliable_guess(g,1.)
            right=check_instrument(g,.50) if n==6 else best_reliable_guess(g,.50)[0]
            marked=.25
            observed=(1-marked)*g+marked
            row['rings'].append(dict(sites=n,occupations=list(g),minimum=small,all_guess=full,
                                     correct_given_half_marked=right/.5,quarter_mark_dark=min(observed),
                                     compatible_echo=(1-small)**2+small**2/n))
        rows.append(row)
    limits=[]
    for x in (.0005,.002,.006):
        tt=transmission(x,maximum=5)
        g6=ring_spectrum(tt,6)
        limits.append(dict(Momega=x,octupole_ratio=(tt[1]/tt[0])/(low_frequency(x,3)/low_frequency(x,2)),
                           six_site_ratio=min(g6)/((2*x)**2/1120)))
    assert abs(limits[0]['six_site_ratio']-1)<.001
    pure=np.array([1.])
    assert abs(min(ring_spectrum(pure,5))-5/16)<2e-14
    assert max(abs(ring_spectrum(pure,6)-np.array([36,24,6,0,6,24])/16))<4e-14
    for k in (1,2,3):
        for n in (5,6,8,10,14):
            analytic=np.zeros(n)
            for m in range(-2*k,2*k+1):
                analytic[m%n]+=comb(4*k,2*k+m)/2**(4*k)
            assert abs(multiple_absorption(pure,n,k)['minimum']-n*min(analytic))<1e-13
    angles=triangle(transmission(.28))
    luminosity=mass_loss()
    for x in (.16,.40,.70):
        larger=transmission(x,maximum=10,even=True)
        for n in (5,6,8):
            np.testing.assert_allclose(ring_spectrum(larger,n),ring_spectrum(transmission(x),n),
                                       rtol=2e-7,atol=5e-13)
    result=dict(atom=atom,frequencies=rows,low_frequency_check=limits,triangle=angles,
                graviton_luminosity=luminosity,geometry= recover_geometry(atom))
    (ROOT/'verification').mkdir(exist_ok=True)
    (ROOT/'verification'/'hawking-absorption-results.json').write_bytes((json.dumps(result,indent=2)+'\n').encode())
    fig,(left,right)=plt.subplots(1,2,figsize=(8.3,3.1),constrained_layout=True)
    for j,n in enumerate((5,6,8)):
        left.semilogy(FREQUENCIES,[r['rings'][j]['minimum'] for r in rows],'-o',ms=3,label=f'{n} sites')
    left.set(xlabel=r'Frequency $GM\omega/c^3$',ylabel='Largest fraction with an exact site label',ylim=(1e-10,1.5))
    left.legend(frameon=False,fontsize=8)
    for i in (2,4,6):
        g=np.array(rows[i]['rings'][1]['occupations'])
        marks=np.linspace(.001,1,180)
        right.plot(marks,[best_reliable_guess(g,p)[0]/p for p in marks],label=f'{FREQUENCIES[i]:.2f}')
    right.set(xlabel='Fraction receiving a label',ylabel='Correct site among labelled events',ylim=(.65,1.025))
    right.legend(title=r'$GM\omega/c^3$',frameon=False,fontsize=8)
    (ROOT/'manuscripts').mkdir(exist_ok=True)
    fig.savefig(ROOT/'manuscripts'/'hawking_absorption_records.pdf',metadata={'CreationDate':None,'ModDate':None})
    plt.close(fig)
    print('Spin-two luminosity',luminosity['total'],'atomic rate',atom['spontaneous_s'],'triangle',angles)


if __name__=='__main__':
    main()
