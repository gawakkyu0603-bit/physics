"""Cosmological stress and nonperturbative flux tests of a completed private contact."""
from math import ceil, cos, exp, pi, sin, sqrt
from pathlib import Path
import json

import numpy as np
from scipy.optimize import minimize_scalar, brentq
from scipy.special import jv, roots_legendre

from landscape_receipts import dataset

ROOT = Path(__file__).resolve().parents[1]


def bao_fit(order):
    z, values, cov = dataset()
    precision = np.linalg.inv(cov)
    nodes, weights = roots_legendre(order)
    grid = z[:, None]*(nodes+1)/2
    quadrature = z[:, None]*weights/2

    def score(dust, t, standard=False):
        # t=x0/(1+x0) compactifies both endpoints of the lapse family.
        def inv_e(redshift):
            b = 1+redshift
            dark = np.ones_like(b) if standard else b**3/(1+t*(b**6-1))**(1/3)
            return 1/np.sqrt(dust*b**3 + (1-dust)*dark)
        dh = inv_e(z)
        dm = np.sum(quadrature*inv_e(grid), axis=1)
        ratios = np.r_[(z[0]*dh[0]*dm[0]**2)**(1/3), np.column_stack((dm[1:],dh[1:])).ravel()]
        scale = (ratios@precision@values)/(ratios@precision@ratios)
        residual = values-scale*ratios
        return float(residual@precision@residual),float(scale)

    def profile(t, standard=False):
        fit = minimize_scalar(lambda d:score(d,t,standard)[0], bounds=(0.,1.),method="bounded",
                              options={"xatol":2e-12})
        return min((score(d,t,standard)[0],d,score(d,t,standard)[1]) for d in (0.,fit.x,1.))
    grid_t = np.linspace(0,1,81)
    vals = [profile(t)[0] for t in grid_t]
    candidates = [0.,1.]
    for j in range(1,len(grid_t)-1):
        if vals[j]<vals[j-1] and vals[j]<vals[j+1]:
            fit = minimize_scalar(lambda t:profile(t)[0],bounds=(grid_t[j-1],grid_t[j+1]),
                                  method="bounded",options={"xatol":2e-12})
            candidates.append(float(fit.x))
    winner = min((profile(t)[0], t, *profile(t)[1:]) for t in candidates)
    vanilla = profile(0.,True)
    return dict(lapse_chi2=winner[0],t_at_minimum=winner[1],ordinary_dust_fraction=winner[2],
                distance_scale=winner[3],flux_and_mass_chi2=vanilla[0],total_matter=vanilla[1],
                flux_and_mass_scale=vanilla[2],distance_count=len(values),
                profile_at_quarters=[[t,*profile(t)] for t in (0,.25,.5,.75,1.)])


def contact_moments():
    # Independent finite Fourier transform and the analytic Bessel distribution.
    angle=2*pi*np.arange(16384)/16384
    wave_numbers=np.fft.fftfreq(len(angle))*len(angle)
    cases=[]
    ratio=sqrt((6/7)*2**(1/3))
    for a in (1.,4.,20.,40.):
        amp=np.fft.fft(np.exp(-1j*a*np.cos(angle)))/len(angle)
        p=abs(amp)**2
        second=float(p@(wave_numbers**2))
        assert abs(second-a*a/2)<2e-10 and abs(p@wave_numbers)<1e-12
        assert abs(p[0]-jv(0,a)**2)<2e-14
        displacement=abs(1000+wave_numbers)
        allowed=(980<displacement)&(displacement<980*ratio)
        direct=sum(jv(n,a)**2 for n in range(-150,151) if 980<abs(1000+n)<980*ratio)
        assert abs(p[allowed].sum()-direct)<1e-13
        cases.append(dict(phase=a,neutral=float(p[0]),signed_mean=float(p@wave_numbers),
                          absolute_mean=float(p@abs(wave_numbers)),second=second,
                          stable_patch_weight=float(p[allowed].sum())))
    return cases


def charged_exchange():
    """Exact open-chain Hamiltonian including the energy of the written flux."""
    from scipy.linalg import eigh_tridiagonal
    examples=[]
    k=1000
    for a,u in ((4.,0.),(4.,pi/(2*k)),(4.,pi/k),(20.,pi/k)):
        # T=hbar=1. The contact hopping is a/2 and u is the cell energy in these units.
        for extent in (60,100):
            n=np.arange(-extent,extent+1)
            hops=np.full(2*extent,a/2)
            def propagate(diagonal):
                ev,vec=eigh_tridiagonal(diagonal,hops)
                amps=vec@(np.exp(-1j*ev)*vec[extent,:])
                return abs(amps)**2
            linear=propagate(2.*k*u*n)
            full=propagate(u*(2*k*n+n*n))
            phase=a*np.sinc(k*u/pi)
            assert max(abs(linear-jv(n,phase)**2))<2e-12
            assert abs(full.sum()-1)<4e-13
            current=float(full@(u*(2*k*n+n*n)))
            assert abs(current)<=abs(a)+1e-10
            if extent==60:
                previous=full.copy()
            else:
                assert max(abs(previous-full[extent-60:extent+61]))<3e-12
                bound=u*(abs(a)/(2*sqrt(2))+sqrt(3/8)*a*a/3)
                assert abs(full[extent]-linear[extent])<=min(1.,bound)+1e-12
                examples.append(dict(contact_phase=a,flux_energy_time=u,
                                     bare_neutral=float(jv(0,a)**2),
                                     linear_neutral=float(linear[extent]),exact_neutral=float(full[extent]),
                                     mean_flux_work=current,amplitude_error_bound=bound))
    return examples


def compensated_exchange():
    """Positive-energy receiver and exact evolution on each fixed total-energy shell."""
    from scipy.linalg import eigh_tridiagonal
    from scipy.stats import poisson
    examples=[]
    for k,margin,a in ((5,0,4.),(5,2,4.),(5,12,4.),(1000,4,4.),(1000,16,4.),(1000,16,40.),(1000,60,40.)):
        radius=k+margin
        modes=2*radius+1
        angles=np.arange(1,modes+1)*pi/(modes+1)
        initial=k+radius+1
        initial_wave=sqrt(2/(modes+1))*np.sin(initial*angles)
        time=np.exp(-1j*a*np.cos(angles))
        from scipy.fft import dst
        full=dst(initial_wave*time,type=1,norm="ortho")
        probability=abs(full)**2
        m=np.arange(-radius,radius+1)
        assert abs(probability.sum()-1)<4e-13
        remainder=radius**2-m*m
        assert min(remainder)==0 and max(abs(m*m+remainder-radius**2))==0
        if k==5:
            ev,vec=eigh_tridiagonal(np.zeros(modes),np.full(modes-1,.5))
            direct=vec@(vec[initial-1]*np.exp(-1j*a*ev))
            assert max(abs(direct-full))<2e-13
        neutral=float(probability[initial-1])
        ideal=float(jv(0,a)**2)
        depth=margin+1
        amp_tail=min(1.,2*exp(abs(a))*poisson.sf(depth-1,abs(a)))
        # Even at small a this simple all-state bound is conservative.
        assert abs(neutral-ideal)<=amp_tail+2e-13
        examples.append(dict(initial=k,radius=radius,margin=margin,phase=a,work_units=radius**2-k*k,
                             neutral=neutral,ideal_neutral=ideal,
                             stable_volume_weight=float(probability[(980<abs(m))&(abs(m)<980*sqrt((6/7)*2**(1/3)))].sum()) if k==1000 else None,
                             uniform_distance_bound=float(amp_tail)))
    return examples


def compact_volume():
    # Four-dimensional Einstein frame.  F=1 specifies an energy unit and
    # the chosen density ratio is illustrative, not a new observational fit.
    casimir=1.45
    target_ratio=.38
    matter=target_ratio*(casimir-4/3)/(1+target_ratio/6)
    curvature=(21+1.5*matter-18*casimir)/9
    vacuum=1-casimir-curvature
    stiffness=252-162*casimir-45*matter/4
    def energy(u):
        return exp(-21*u)-curvature*exp(-9*u)-casimir*exp(-18*u)+matter*exp(-1.5*u)
    hstep=1e-5
    assert abs((energy(hstep)-energy(-hstep))/(2*hstep))<2e-7
    assert abs((energy(hstep)-2*energy(0)+energy(-hstep))/hstep**2-stiffness)<2e-5
    ratio=sqrt((6/7)*2**(1/3))
    # Set A=1, k_M=980, and y_M=1 to fix C and the positive curvature-energy coefficient.
    k_m=980.; coef_c=4*k_m**2/3; coef_r=coef_c/4
    brackets=[]
    for k in (970,980,995,1000,1010,1018,1019,1030):
        saddle_y=9*coef_c/(14*k*k)
        eq=lambda y:7*k*k*y**4-6*coef_c*y**3+3*coef_r
        if eq(saddle_y)>0:
            brackets.append([k,"no stationary point"]);continue
        y=brentq(eq,saddle_y,3.)
        vacuum_ratio=(k*k*y**7-coef_c*y**6+coef_r*y**3)/(k*k*y**7)
        brackets.append([k,"positive minimum" if vacuum_ratio>1e-10 else
                         "negative minimum" if vacuum_ratio < -1e-10 else "zero minimum",vacuum_ratio])
    return dict(casimir_over_flux=casimir,wrapped_dust_over_flux=matter,curvature_signed=curvature,
                vacuum_over_flux=vacuum,curvature_stiffness=stiffness,
                radion_mass_over_H=sqrt((2/21)*stiffness/(vacuum+matter)),
                unscreened_force_to_Newton=1/7, fold_to_zero_flux=ratio,
                minimum_continuous_k_for_both_unit_steps=2/(ratio-1),
                minimum_continuous_k_for_both_191_steps=382/(ratio-1), examples=brackets)


def exterior_membrane():
    """Unseeded zero-mass thin shell between fixed-radius flux domains, M_P=1."""
    k_m=980.0
    c3=4*k_m**2/3
    curvature=c3/4
    probes=[]
    for k in (981,995,1000,1010,1018):
        y=brentq(lambda s:7*k*k*s**4-6*c3*s**3+3*curvature,
                 9*c3/(14*k*k),3.)
        tension=y**3.5
        flux=k*k*tension**2
        eta=(flux-c3*y**6+curvature*y**3)/flux
        v=3*eta/4
        assert abs((k/k_m)**6-(1+8*v)/(1+v)**4)<5e-11
        assert eta>=2*(k/k_m-1)-1e-12
        h_out2=eta*flux/3
        release=(2*k-1)*tension*tension
        h_in2=h_out2-release/3
        # Reconstruct the unsquared junction equation, also if the interior is AdS.
        radius=1/sqrt(h_out2+(release/(3*tension)-tension/4)**2)
        outer=sqrt(1-h_out2*radius**2)
        inner=sqrt(1-h_in2*radius**2)
        assert abs((inner-outer)-tension*radius/2)<3e-14
        fraction=radius*sqrt(h_out2)
        assert abs(fraction-sqrt(eta/(eta+(8*k-7)**2/(48*k*k))))<3e-15
        for margin in range(1,min(k-981,1018-k)+1):
            assert fraction**2>3*margin/(2*k+3*margin)
        probes.append(dict(k=k,eta=eta,radius_in_Hubble_units=fraction,
                           largest_symmetric_positive_margin=min(k-981,1018-k),
                           example_bound_16=sqrt(48/(2*k+48)) if 980<k-16 and k+16<980*sqrt((6/7)*2**(1/3)) else None))
    return probes


def subdivision():
    # A normalized heat kernel and a Brownian motion plus symmetric Poisson jumps.
    max_error=0.
    for t in (0.02,.3,1.4,3.):
        for jump in (.03,.8,pi):
            d,rate=.713,.42
            psi=lambda k:d*k*k+rate*(2*sin(k*jump/2)**2)
            gap=4*psi(1)-psi(2)
            four=2*rate*(1-cos(jump))**2
            assert abs(four-gap)<1e-14
            for k in range(2,40):
                deficit=k*k*psi(1)-psi(k)
                assert -4e-12<=deficit<=k*k*(k*k-1)*gap/12+2e-9
                max_error=max(max_error,abs(exp(-.4*t*psi(k))*exp(-.6*t*psi(k))-exp(-t*psi(k))))
    # Check actual gluing by integrating two kernels over a shared 3-face.
    angles=2*pi*np.arange(512)/512
    k=np.arange(1,50)
    def heat(a,t):
        return 1+2*(np.cos(np.outer(a,k))@np.exp(-t*k*k))
    convolution=np.mean(heat(angles,.14)*heat(.93-angles,.09))
    assert abs(convolution-heat(np.array([.93]),.23)[0])<2e-15
    parity=[0.5*k*k + 0.25*(1-(-1)**k) for k in (1,2,3)]
    assert parity == [1.0,2.0,5.0]
    return dict(max_semigroup_error=max_error,shared_face_integral=float(convolution),
                parity_jump_example=parity, sharp_coefficients=[k*k*(k*k-1)/12 for k in (2,3,10,191)])


def matrix_match():
    # Exact nonperturbative clock-shift configuration; principal angles in (-pi,pi).
    direct=[]
    for rank,flux in ((13,1),(29,-5),(47,11)):
        u=np.diag(np.exp(2j*pi*flux*np.arange(rank)/rank))
        v=np.roll(np.eye(rank),1,axis=0)
        plaquette=u@v@u.conj().T@v.conj().T
        angle=np.angle(np.linalg.eigvals(plaquette)); b=float(sum(angle)/(2*pi))
        lattice=rank/(2*pi*pi)*np.trace(np.eye(rank)-(plaquette+plaquette.conj().T)/2).real
        assert abs(b-flux)<3e-13 and abs(lattice-(flux*np.sinc(flux/rank))**2)<5e-13
        direct.append([rank,flux,b,float(lattice)])
    m=191
    first=next(n for n in range(2*m+1,10000) if np.sinc(m/n)**2>.99)
    return dict(plaquette_examples=direct,first_rank_one_percent=first,
                conservative_rank=ceil(pi*m/sqrt(.03)), barrier_in_cell_energy_at_first=first/pi**2,
                relative_energy_error_at_first=float(1-np.sinc(m/first)**2))


def main():
    fits=bao_fit(80)
    doubled=bao_fit(160)
    assert abs(fits['lapse_chi2']-doubled['lapse_chi2'])<1e-7
    # Pressure from independent derivatives of the energy at three densities.
    for n in (.2,1.,4.):
        h=1e-4*n
        rho=lambda x:x/(1+x*x)**(1/3)
        pressure=lambda x:-(2/3)*(x*x)/(1+x*x)*rho(x)
        sound=-(2/3)*n*n*(n*n+9)/((1+n*n)*(3+n*n))
        assert abs(n*(rho(n+h)-rho(n-h))/(2*h)-rho(n)-pressure(n))<1e-8
        assert abs((pressure(n+h)-pressure(n-h))/(rho(n+h)-rho(n-h))-sound)<1e-8
    result=dict(bao=fits,cosine_contact=contact_moments(),einstein_frame=compact_volume(),
                flux_kernel=subdivision(),matrix=matrix_match(),charged_exchange=charged_exchange(),
                compensated_exchange=compensated_exchange(),external_M2=exterior_membrane())
    (ROOT/'verification'/'dark-record-action-results.json').write_text(
        json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print('DESI compressed table:',fits['lapse_chi2'],fits['flux_and_mass_chi2'])
    print('Static positive radion interval ratio:',result['einstein_frame']['fold_to_zero_flux'])
    print('First matrix rank:',result['matrix']['first_rank_one_percent'])


if __name__=='__main__':
    main()
