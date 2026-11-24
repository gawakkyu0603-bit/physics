"""Dyonic endpoints, the wrapped charge lattice and a magnetic KK horizon."""
from decimal import Decimal, getcontext
from itertools import combinations, product
from pathlib import Path
import json
import math
import os

import numpy as np
from scipy.integrate import solve_ivp
from scipy.special import gammaln, loggamma

ROOT=Path(__file__).resolve().parents[1]


def cochain_check():
    """Keep the ordered cup product and real lifts of circle connections."""
    cells={k:list(combinations(range(6),k+1)) for k in range(5)}
    def d(co):
        dim=len(next(iter(co)))
        return {s:sum((-1)**j*co[s[:j]+s[j+1:]] for j in range(len(s)))
                for s in cells[dim]}
    def add(a,b,sign=1):
        return {s:u+sign*b[s] for s,u in a.items()}
    def integral(a,b):
        k=len(next(iter(a)))-1
        return sum((-1)**i*a[s[:k+1]]*b[s[k:]] for i,s in enumerate(reversed(cells[4])))
    rng=np.random.default_rng(109)
    residual=0.
    detected=0
    for _ in range(96):
        one=[{s:rng.normal() for s in cells[1]} for _ in range(2)]
        sheets=[{s:int(rng.integers(-2,3)) for s in cells[2]} for _ in range(2)]
        moves=[{s:int(rng.integers(-3,4)) for s in cells[1]} for _ in range(2)]
        def paired(a,b):
            f=[add(d(aa),bb) for aa,bb in zip(a,b)]
            bulk=integral(b[0],b[1])
            ends=integral(a[0],d(b[1]))-integral(d(b[0]),a[1])
            return integral(*f),bulk,ends
        before=paired(one,sheets)
        after=paired([add(aa,l,-1) for aa,l in zip(one,moves)],
                     [add(bb,d(l)) for bb,l in zip(sheets,moves)])
        detected+=(before[1]-after[1])%2
        residual=max(residual,abs(before[0]-after[0]),abs(before[0]-sum(before[1:])),
                     abs(after[0]-sum(after[1:])))
    assert residual<3e-13 and detected>20
    return dict(trials=96,uncompensated_sign_changes=int(detected),
                completed_exponent_max_error=residual)


def moduli_check():
    y0=math.sqrt(3)/2
    def energy(x,y):
        return (1+math.hypot(x,y)+math.hypot(1-x,y))/math.sqrt(y)
    e0=energy(.5,y0)
    step=2e-4
    xx=(energy(.5+step,y0)+energy(.5-step,y0)-2*e0)/step**2
    yy=(energy(.5,y0+step)+energy(.5,y0-step)-2*e0)/step**2
    ratios=np.array([xx,yy])*y0*y0/e0
    assert max(abs(ratios-3/8))<3e-7
    mid=complex(.5,y0)
    low=complex(.5,1/(2*math.sqrt(3)))
    assert abs(2-1/low-mid)<1e-14
    dual=[(-1/r).real for r in (mid,low)]
    assert np.allclose(dual,[-.5,-1.5])
    other=mid/(2*mid+1)
    assert abs(other.real-5/14)<1e-14
    # Independently compute the full two-vector inverse coupling.
    a,b=1.7,.91
    tau=np.array([[1j*y0*b/a,.5],[.5,1j*y0*a/b]])
    swapped=tau[np.ix_([1,0],[1,0])]
    assert np.linalg.norm(-np.linalg.inv(tau)+np.array([[0,1],[1,0]])-swapped)<8e-16
    grid=np.arange(-38,39)
    k,p=np.meshgrid(grid,grid,indexing="ij")
    def thermal(x,y,beta):
        masses=np.sqrt((k+p*x)**2/y+p*p*y)
        return float(np.exp(-2*beta*masses).sum()-1)
    comparisons=[]
    for beta in [1.,2.,4.]:
        zhex=thermal(.5,y0,beta)
        zsquare=thermal(0.,1.,beta)
        za=thermal(.5,.7,beta)
        assert min(zsquare,za)>zhex
        comparisons.append([beta,zhex,zsquare,za])
    minima=[energy(x,y) for x in np.linspace(-.3,1.3,41) for y in np.linspace(.32,2.,43)]
    assert min(minima)>=e0-3e-12
    def gradients(k,p):
        t=k+p*mid.real
        d=t*t+(p*y0)**2
        return np.array([y0*p*t/d,y0*y0*p*p/d-.5])
    g=np.array([gradients(k,p) for k,p in [(1,0),(-1,1),(0,-1)]])
    assert np.linalg.norm(g.sum(axis=0))<1e-15
    assert np.allclose(g@g.T, np.full((3,3),-1/8)+np.eye(3)*3/8)
    count=np.array([7,4,8])
    charge=2*np.sum(count[:,None]*g,axis=0)/sum(count)
    charge_bound=sum((count[i]-count[(i+1)%3])**2 for i in range(3))/(2*sum(count)**2)
    assert abs(charge@charge-charge_bound)<2e-16
    return dict(hexagon_y=y0,second_representative_y=low.imag,dual_real_parts=dual,
                another_polarization_real=other.real, normalized_frozen_energy=e0,
                physical_hessian_over_energy=ratios.tolist(),thermal_pairs=comparisons,
                squared_scalar_charge_example=float(charge_bound))


def receiver_check():
    theta=math.pi/3
    critical=math.sqrt(2*math.pi*theta)
    force_ratio=12/1225
    probability=.5*(1+math.sin(.5*math.pi*force_ratio))
    far=3.
    ratio=((far-.5)**-2-(far+.5)**-2)/8
    assert abs(ratio-force_ratio)<1e-16
    # In scaled time s=sqrt(v/(2*pi*alpha')) t: u''+(s^2+a)u=0.
    # Compare both signs of mass squared and the critical crossing to the
    # Weber connection formula, by evolving one normalized adiabatic mode.
    def weber(a,end):
        def asymptote(s):
            w=math.sqrt(s*s+a)
            # Second order adiabatic frequency.
            wp=s/w
            wpp=a/w**3
            ad=w-wpp/(4*w*w)+3*wp*wp/(8*w**3)
            da=wp+5*a*s/(4*w**7)+(3/8)*(2*s/w**5-5*s**3/w**7)
            return np.array([1/math.sqrt(2*ad),(-1j*ad-da/(2*ad))/math.sqrt(2*ad)])
        sol=solve_ivp(lambda s,h:(h[1],-(s*s+a)*h[0]),[-end,end],asymptote(-end),
                      method="DOP853",rtol=2e-11,atol=1e-12)
        assert sol.success
        out=asymptote(end)
        coeff=np.linalg.solve(np.column_stack([out,out.conj()]),sol.y[:,-1])
        return abs(coeff[1])**2,abs(abs(coeff[0])**2-abs(coeff[1])**2-1)
    samples=[]
    for a in [-.35,0.,.45]:
        value,wronskian=weber(a,23)
        ref=math.exp(-math.pi*a)
        assert abs(value/ref-1)<2e-7 and wronskian<3e-8
        samples.append([a,value,ref,wronskian])
    return dict(binding_fraction=1-math.sqrt(3)/2,relative_angle=theta,
                critical_distance_in_string_lengths=critical,force_ratio_at_three=force_ratio,
                far_sign_success_for_perfect_midpoint=probability,weber=samples)


def get_poly(poly,i):
    return poly[i] if 0<=i<len(poly) else 0


def radial_probability(h,n,j,omega=math.sqrt(2),magnetic=1,outer=54,order=6):
    """Ingoing Frobenius solution, matched to two Coulomb waves; R_circle=1."""
    p=math.sqrt(omega*omega-n*n)
    a=magnetic**2/(2*(math.hypot(h,magnetic)+h))
    q=n*magnetic/2
    angular=j*(j+1)-q*q
    rho=-1j*omega*math.sqrt(h*(h+a))
    b1=omega*omega*h*(2*h+a)-(h+a)**2*n*n-angular
    first=-(rho+b1)/(1+2*rho)
    z0=1e-7
    u=z0**rho*(1+first*z0)
    v=z0**rho*(rho+(1+rho)*first*z0)
    def radial(y,state):
        z=math.exp(y)
        r=h*(1+z)
        f=z/(1+z)
        potential=omega*omega*r*(r+a)-f*((r+a)**2*n*n+angular)
        return [state[1],-f*state[1]-potential*state[0]]
    sol=solve_ivp(radial,[math.log(z0),math.log(outer/h-1)],[u,v],
                  method="DOP853",rtol=3e-11,atol=1e-12)
    assert sol.success
    rad,dy=sol.y[:,-1]
    ufar=outer*rad
    dufar=rad+outer*dy/(outer-h)
    aa=[1,-2*h,h*h]
    bb=[0,0,h,-h*h]
    cc=[p*p,a*omega**2-(2*a-h)*n*n,(2*h*a-a*a)*n*n-angular,
        h*a*a*n*n+h*angular-h,h*h]
    alpha=(cc[1]-p*p*aa[1])/(2*p)
    def term(nu,d):
        return (-p*p*get_poly(aa,d)+2j*p*nu*get_poly(aa,d-1)+nu*(nu-1)*get_poly(aa,d-2)
                +1j*p*get_poly(bb,d)+nu*get_poly(bb,d-1)+get_poly(cc,d))
    tail=[1.+0j]
    for k in range(1,order+1):
        tail.append(sum(b*term(1j*alpha-i,k+1-i) for i,b in enumerate(tail))/(2j*p*k))
    phase=np.exp(1j*p*outer)*outer**(1j*alpha)
    out=phase*sum(b*outer**(-i) for i,b in enumerate(tail))
    dout=phase*sum(b*outer**(-i)*(1j*p+(1j*alpha-i)/outer) for i,b in enumerate(tail))
    incoming,outgoing=np.linalg.solve([[out.conjugate(),out],[dout.conjugate(),dout]],[ufar,dufar])
    prob=omega*h*math.sqrt(h*(h+a))/(p*abs(incoming)**2)
    residual=abs(1-abs(outgoing/incoming)**2-prob)
    return float(prob),float(residual)


def asymptotic(h,n,j,omega=math.sqrt(2),magnetic=1):
    ell=abs(magnetic)/2
    p=math.sqrt(omega**2-n*n)
    eta=-ell*(omega**2-2*n*n)/(2*p)
    logc=j*math.log(2)-math.pi*eta/2+loggamma(j+1.+1j*eta).real-gammaln(2*j+2)
    logl=gammaln(2*j+1)-2*gammaln(j+1)
    return 4*math.exp(2*(logc-logl))*omega*p**(2*j+1)*h**(2*j+1.5)*math.sqrt(ell)


def channel_law(tau,occupancy):
    noise=tau*occupancy
    absorb=(tau+noise)/(1+noise)**2
    odd=(tau+3*noise+2*noise**2)/(1+2*noise)**2
    return absorb,odd,noise/(1+2*noise)


def horizon_checks():
    hs=[.2,.05,.01,.002,.0004,.00008,.000016,.0000032]
    data=[]
    err=bal=0.
    leading=math.pi**2/128*(-math.expm1(-math.pi/math.sqrt(2)))
    for h in hs:
        row=[]
        for n,j in [(0,0),(1,.5)]:
            actual,e=radial_probability(h,n,j)
            other,_=radial_probability(h,n,j,outer=79,order=8)
            bal=max(bal,e)
            err=max(err,abs(other/actual-1))
            row.append((actual,asymptotic(h,n,j)))
        a=1/(2*(math.hypot(h,1)+h))
        occupation=1/math.expm1(4*math.pi*math.sqrt(2*h*(h+a)))
        tau=row[1][0]
        absorb,odd,false=channel_law(tau,occupation)
        data.append(dict(h=h,neutral=row[0][0],charged=tau,neutral_over_leading=row[0][0]/row[0][1],
                         charged_over_leading=tau/row[1][1],ratio_over_h=tau/(h*row[0][0]),
                         mean_horizon_occupation=occupation,odd_write=odd,empty_odd=false,
                         pure_absorption_given_odd=absorb/odd))
    assert err<4e-8 and bal<2e-8
    assert abs(data[-1]["ratio_over_h"]/leading-1)<.001
    assert max(abs(data[-1][k]-1) for k in ["neutral_over_leading","charged_over_leading"])<.001
    assert abs(data[-1]["pure_absorption_given_odd"]-1/3)<.008
    return dict(rows=data,matched_ratio_coefficient=leading,
                matching_relative_error=err,flux_absolute_error=bal)


def thermal_checks():
    # Explicit two-mode Fock amplitudes for |1,k>; compare with the thermal
    # generating function. A binomial recurrence avoids large factorials.
    from scipy.special import comb
    tests=[]
    for tau,mean in [(.12,.8),(.38,1.4),(.77,.22)]:
        reflection=math.sqrt(1-tau)
        transfer=math.sqrt(tau)
        weights=np.zeros(102)
        for k in range(100):
            prior=(mean/(1+mean))**k/(1+mean)
            for l in range(k+2):
                # Multiply (r a†+t b†)(-t a†+r b†)^k/sqrt(k!).
                c1=math.sqrt(l*comb(k,l-1))*reflection*(-transfer)**(l-1)*reflection**(k-l+1) if l>0 else 0.
                c2=math.sqrt((k-l+1)*comb(k,l))*transfer*(-transfer)**l*reflection**(k-l) if l<=k else 0.
                weights[l]+=prior*(c1+c2)**2
        a,p,_=channel_law(tau,mean)
        assert abs(sum(weights)-1)<2e-13 and abs(weights[0]-a)<1e-14
        assert abs(sum(weights[::2])-p)<1e-14
        assert abs(np.arange(len(weights))@weights-((1-tau)+tau*mean))<2e-13
        tests.append([tau,mean,a,p])
    getcontext().prec=55
    thresholds=[]
    for digits in [5,8,11]:
        xi=Decimal(10)**(-digits)
        unit=1/(8*xi)
        extremal=(unit**(Decimal(2)/3)+1)**(Decimal(3)/2)
        target=8*xi*(extremal-Decimal(2).sqrt())
        # sqrt(1+h*h)+3*h=target, rationalized positive root.
        h=(target*target-1)/(3*target+(target*target+8).sqrt())
        assert abs((1+h*h).sqrt()+3*h-target)<Decimal("1e-44")
        thresholds.append([float(xi),float(h),float(h/(2*xi**(Decimal(2)/3)))])
    assert abs(thresholds[-1][2]-1)<.001
    return dict(fock_mode_checks=tests,extremal_energy_thresholds=thresholds)


def charge_readout():
    """Enumerate actual receipts and the four possible compact charge parities."""
    directions = [(0, 0), (1, 0), (0, 1), (1, 1)]

    def intersection(q, w):
        return (q[0] * w[1] - q[1] * w[0]) % 2

    def information(indices):
        answers = {tuple(intersection(q, directions[i]) for i in indices)
                   for q in directions}
        return len(answers).bit_length() - 1

    rows = []
    for probabilities, count in [((.25, .25, .25, .25), 3),
                                 ((.6, .1, .2, .1), 6),
                                 ((.4, .6, 0., 0.), 7),
                                 ((1., 0., 0., 0.), 2)]:
        ranks = np.zeros(3)
        survives = np.zeros(3)
        for sequence in product(range(4), repeat=count):
            weight = math.prod(probabilities[i] for i in sequence)
            if weight == 0:
                continue
            measured = set(sequence)
            ranks[information(measured)] += weight
            for i, charge in enumerate(directions[1:]):
                if all(intersection(charge, directions[j]) == 0 for j in measured):
                    survives[i] += weight
        empty = probabilities[0] ** count
        parallel = np.array([(probabilities[0] + p) ** count for p in probabilities[1:]])
        expected = [empty, parallel.sum() - 3*empty, 1 - parallel.sum() + 2*empty]
        assert np.allclose(ranks, expected, atol=2e-13, rtol=0)
        assert np.allclose(survives, parallel, atol=2e-13, rtol=0)
        entropy = float(ranks @ [2., 1., 0.])
        assert abs(entropy - (parallel.sum() - empty)) < 2e-13
        rows.append(dict(packets=count, probabilities=probabilities,
                         rank_probabilities=ranks.tolist(), remaining_bits=entropy))
    return rows


def continuous_recoil():
    """Check infinite mode counts and finite-energy continuum posterior widths."""
    from scipy.integrate import quad
    from scipy.special import ndtr, roots_hermitenorm, roots_legendre

    tails = []
    for tau, occupancy, cutoff in [(.31, .82, 5), (.74, 3.2, 10), (.08, .15, 3)]:
        noise = tau * occupancy
        b = noise / (1 + noise)
        counts = np.arange(450)
        pdf = b**counts * (tau + noise + (1-tau)*counts/noise) / (1+noise)**2
        tail = b**cutoff * (1 + (1-tau)*cutoff/(noise*(1+noise)))
        assert abs(pdf.sum()-1) < 2e-14
        assert abs(pdf[cutoff:].sum()-tail) < 5e-14
        assert abs(pdf[::2].sum()-channel_law(tau, occupancy)[1]) < 2e-14
        tails.append(dict(transmission=tau, thermal_mean=occupancy, cutoff=cutoff,
                          tail=float(tail)))

    nodes, weights = roots_legendre(85)
    noise_nodes, noise_weights = roots_hermitenorm(82)
    sqrt_two_pi = math.sqrt(2*math.pi)
    widths = []
    for sigma in [.15, 1., 3.]:
        def density_mean(p):
            x = np.abs(p)
            high, low = (1-x)/sigma, (-1-x)/sigma
            window = ndtr(high)-ndtr(low)
            deriv = (np.exp(-low**2/2)-np.exp(-high**2/2)) / (sigma*sqrt_two_pi)
            mean = np.sign(p)*(x + sigma*sigma*deriv/window)
            return window/2, mean

        def second_moment(p):
            density, mean = density_mean(p)
            return density*mean*mean

        # Law of total variance, then an independent integral of squared error.
        norm = 2*quad(lambda p: density_mean(p)[0], 0, 1+10*sigma, epsabs=2e-13)[0]
        mmse = 1/3 - 2*quad(second_moment, 0, 1+10*sigma, epsabs=2e-13)[0]
        readings = nodes[:, None] + sigma*noise_nodes[None, :]
        _, post = density_mean(readings)
        direct = float((weights/2) @ (nodes[:, None]-post)**2 @ (noise_weights/sqrt_two_pi))
        linear = sigma*sigma/(1+3*sigma*sigma)
        assert abs(norm-1) < 3e-13 and abs(direct-mmse) < 2e-10
        assert 0 < mmse <= linear + 1e-13
        widths.append(dict(pointer_sigma_over_momentum=sigma, remaining_fraction=3*mmse,
                           linear_bound=3*linear, quadrature_difference=abs(direct-mmse)))
    return dict(canonical_tails=tails, continuum_widths=widths)


def tensor_scattering(x, wave_radius, order, ell=2, spin=2):
    """Return Schwarzschild transmission and reflection for an axial spin-s wave."""
    angular = ell * (ell + 1)
    spin_term = spin**2-1
    start = 1e-7
    start_r = 1+start
    start_star = start_r + math.log(start)
    slope = (angular-spin_term)/(1-2j*x)
    phase = np.exp(-1j*x*start_star)
    psi = phase*(1+slope*start)
    momentum = -1j*x*psi + phase*start/start_r*slope

    def equation(y, state):
        r = 1 + math.exp(y)
        f = (r-1)/r
        potential = f*(angular/r**2-spin_term/r**3)
        return r*state[1], r*(potential-x*x)*state[0]

    outer = wave_radius/x
    solution = solve_ivp(equation, [math.log(start), math.log(outer-1)],
                         [psi, momentum], method="DOP853", rtol=2e-11, atol=2e-13)
    assert solution.success
    coeff = [1.+0j]
    for k in range(1, order+1):
        lower = coeff[k-2] if k >= 2 else 0.
        coeff.append(((k*(k-1)-angular)*coeff[-1]+(spin_term-k*(k-2))*lower)/(2j*x*k))
    tail = np.array([c/outer**k for k,c in enumerate(coeff)])
    outgoing = np.exp(1j*x*(outer+math.log(outer-1)))*sum(tail)
    derivative = 1j*x*outgoing - (1-1/outer)/outer*sum(np.arange(len(tail))*tail)*np.exp(1j*x*(outer+math.log(outer-1)))
    incoming, reflected = np.linalg.solve([[outgoing.conjugate(), outgoing],
                                            [derivative.conjugate(), derivative]],
                                           solution.y[:, -1])
    return 1/incoming, reflected/incoming


def tensor_horizon(x, wave_radius, order):
    """Spin-two quadrupole transmission and reflection probabilities."""
    transmitted, reflected = tensor_scattering(x, wave_radius, order)
    return abs(transmitted)**2, abs(reflected)**2


def tensor_reception():
    from scipy.integrate import quad
    densities = [lambda v: 5*(1+v)**4/32, lambda v: 5*(1-v)**4/32,
                 lambda v: 5*(1+6*v*v+v**4)/32]
    moments = [[quad(lambda v: v**j*density(v), -1, 1)[0] for j in (0,1,2)]
               for density in densities]
    assert np.allclose(moments, [[1,2/3,11/21], [1,-2/3,11/21], [1,0,11/21]])
    rows = []
    # One selected circular-polarization port and a ringdown-free incident packet.
    overlap = .005
    for x in [.12, .04, .012, .003, .00075, .0001875]:
        tau, refl = tensor_horizon(x, 34, 7)
        check, _ = tensor_horizon(x, 50, 9)
        assert abs(check/tau-1) < 3e-7
        assert abs(1-refl-tau) < 1e-8
        occupation = 1/math.expm1(4*math.pi*x)
        noise = tau*occupation
        gain, odd, vacant = channel_law(tau, occupation)
        odd_mix = overlap*odd+(1-overlap)*vacant
        chi = overlap*gain/odd_mix
        difference = overlap*(tau+2*noise)/(1+2*noise)**2
        assert abs(odd_mix-vacant-difference) < 1e-14*odd_mix
        rows.append(dict(omega_radius=x, transmission=tau,
                         relative_to_leading=tau/(4*x**6/225),
                         check_relative=abs(check/tau-1),
                         gain_given_odd=chi, odd_excess=difference))
    assert abs(rows[-1]["relative_to_leading"]-1) < .002
    assert abs(rows[-1]["gain_given_odd"]/(overlap/(1+2*overlap))-1) < .003
    return dict(angular_moments=moments, overlap=overlap, soft_fraction=overlap/(1+2*overlap),
                radial=rows)


def draw(result):
    os.environ.setdefault("MPLCONFIGDIR",str(ROOT/".research-tools"/"matplotlib"))
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig,ax=plt.subplots(1,2,figsize=(8.6,3.12),layout="constrained")
    y=np.linspace(.4,1.6,250)
    y0=math.sqrt(3)/2
    def rest(a):
        return (1+2*np.sqrt(.25+a*a))/np.sqrt(a)
    grid=np.arange(-20,21)
    k,p=np.meshgrid(grid,grid)
    def free(a):
        return -math.log(np.exp(-4*np.sqrt((k+.5*p)**2/a+p*p*a)).sum()-1)/2
    ax[0].plot(y,rest(y)-rest(y0),label="Frozen neutral triplet",color="#28577c",lw=2)
    ax[0].plot(y,[free(a)-free(y0) for a in y],label="Equilibrated neutral pair",color="#ad572b",lw=2)
    ax[0].axvline(y0,color=".45",ls=":",lw=1)
    ax[0].set(xlabel="Torus area in string units",ylabel="Energy change / mass scale")
    ax[0].legend(frameon=False,fontsize=8)
    rows=result["horizon"]["rows"]
    hs=[r["h"] for r in rows]
    ax[1].loglog(hs,[r["neutral"] for r in rows],marker="o",ms=3,label="Neutral, j = 0",color="#28577c")
    ax[1].loglog(hs,[r["charged"] for r in rows],marker="s",ms=3,label="Charged, j = 1/2",color="#ad572b")
    ax[1].set(xlabel="Horizon coordinate radius / circle radius",ylabel="Transmission per incident mode")
    ax[1].legend(frameon=False,fontsize=8)
    for axis in ax:
        axis.spines[["top","right"]].set_visible(False)
    dest=ROOT/"manuscripts"/"natural_flux_endpoints.pdf"
    dest.parent.mkdir(parents=True,exist_ok=True)
    fig.savefig(dest,metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)


def main():
    result=dict(cochain=cochain_check(),modulus=moduli_check(),material=receiver_check(),
                horizon=horizon_checks(),quantum=thermal_checks(),received_directions=charge_readout(),continuous=continuous_recoil(),tensor=tensor_reception())
    dest=ROOT/"verification"/"natural-flux-endpoints-results.json"
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf8")
    draw(result)
    print(json.dumps(result,indent=2))


if __name__=="__main__":
    main()
