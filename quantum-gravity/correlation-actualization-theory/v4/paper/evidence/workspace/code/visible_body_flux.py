"""Thermal stress flux from a visible infaller and the finite gravitational clock."""
from math import expm1, pi, sqrt
from pathlib import Path
import json
import numpy as np
from scipy.constants import G, c, hbar, Boltzmann
from scipy.integrate import quad

ROOT = Path(__file__).resolve().parents[1]


def early_exposure(solar_masses, b_fraction=.1):
    radius = 2*G*(1.98847e30*solar_masses)/c**2
    def integrand(x):
        beta = 1/sqrt(x)
        s2 = b_fraction**2*(1-1/x)/x**2
        co = sqrt(1-s2)
        return sqrt(x)*s2*(1+beta)/(2*(1+co)*(1-beta*co))
    return radius, radius/c*quad(integrand,3,5)[0]


def thermal_source(area, temperature, emissivity, solar_masses):
    radius, exposure = early_exposure(solar_masses)
    band = quad(lambda x:x*x/expm1(x),1,2)[0]
    surface_flux = (Boltzmann*temperature/hbar)**3*band/(4*pi*pi*c*c)
    observed = emissivity*area*surface_flux*exposure
    occupation_max = 1/expm1(1)
    # On this narrow cone the two angularly symmetric arms share a redshift.
    # Every counted conserved energy is in [1.4, 3.2] kT for e=1.
    bound_constant = 2*(3.2/1.4)*sqrt(pi*(1+4*occupation_max)/2)
    gate_min = pi*hbar/(3.2*Boltzmann*temperature)
    return dict(area_m2=area, temperature_K=temperature, emissivity_floor=emissivity,
                black_hole_solar_masses=solar_masses, early_seconds=exposure,
                surface_band_flux_m2_s=surface_flux, mean_absorbed=observed,
                radial_upper=min(1.,bound_constant/sqrt(observed)), constant=bound_constant,
                gate_min_asymptotic_s=gate_min, radius_m=radius,
                finite_clock_256_radial_upper=min(1.,1/256+bound_constant/(2*sqrt(observed))),
                fourier_clock_bandwidth_J=2*pi*hbar*255/gate_min,
                min_radius_for_one_percent_m=sqrt((bound_constant/.01)**2/
                                                 (4*pi*emissivity*surface_flux*exposure)),
                visible_tube_clock_budget_s=sqrt(1-1/1.05)*(1.6091616866624159-.3851315640206487)*radius/c)


def common_clock():
    # Exact thermal splitting of one input mode into two arms and loss.
    n,p=.28,.12
    theta=.73
    ratio=n/(1+n)
    brute=sum((1-ratio)*ratio**k*(1-2*p+2*p*np.cos(theta))**k for k in range(65))
    exact=1/(1+2*n*p*(1-np.cos(theta)))
    assert abs(brute-exact)<2e-15
    # Multiple independent thermal modes. Direct integration of the finite
    # clock vs explicit convolution of physical energy differences on a lattice.
    axis=np.arange(2048)
    phases=2*pi*axis/len(axis)
    weights=np.array([1,2,3])
    mus=np.array([.6,.2,.12])
    repeats=np.array([7,3,4])
    def thermal_character(t):
        return np.prod((1+mus*(1-np.cos(weights*t)))**(-repeats))
    samples=np.array([thermal_character(t) for t in phases])
    mass=np.fft.ifft(samples).real
    charges=np.fft.fftfreq(len(axis))*len(axis)
    comparisons=[]
    for duration in (.4,1.2,8.,25.):
        spectral=sum(mass*np.sinc(charges*duration/(2*pi))**2)
        direct=quad(lambda t:2/duration*(1-t/duration)*thermal_character(t),0,duration,
                    epsabs=1e-12,limit=300)[0]
        assert abs(direct-spectral)<3e-13
        comparisons.append([duration,direct])
    finite=[]
    for size in (16,64,256):
        times=np.arange(size)*1.2/size
        pair_sum=np.mean([thermal_character(t-s)
                          for t in times for s in times])
        direct=sum(mass*np.abs(np.mean(np.exp(-1j*np.outer(charges,times)),axis=1))**2)
        assert abs(direct-pair_sum)<5e-13
        finite.append([size,float(pair_sum)])
    return dict(split_error=float(abs(brute-exact)),clock=comparisons,finite_clocks=finite)


def local_patch(radius, temperature, emissivity):
    # Planar Lambertian patch, no lateral collection from other horizon generators assumed.
    band = quad(lambda k:k*k/expm1(k),1,2)[0]
    flux=(Boltzmann*temperature/hbar)**3*band/(4*pi*pi*c*c)
    cosine=15/17
    mean=emissivity*pi*(radius/2)**2*flux*(1-cosine**2)*radius/c
    return dict(patch_radius_m=radius,near_interval_s=radius/c,photons_within_footprint=mean,
                minimum_lead_s=cosine/(1+cosine)*radius/c)


def elastic_and_direct(solar_masses, mass):
    # Leading horizon quadrupole heating on a slow Newtonian radial plunge, not a graviton count.
    radius_m=G*1.98847e30*solar_masses/c**2
    rho=20.
    energy = (64*sqrt(2)/25)*(mass*c*c)*(mass/(1.98847e30*solar_masses))*rho**(-7.5)
    def integrand(u):
        return (96/5)*sqrt(2)*u**(-8.5)
    dim = quad(integrand, rho,np.inf,epsabs=1e-20)[0]
    assert abs(dim/((64*sqrt(2)/25)*rho**(-7.5))-1)<1e-10
    return dict(source_mass_kg=mass, cutoff_in_GM_c2=rho, heat_J=energy,
                characteristic_frequency_s=sqrt(2)*c/radius_m*rho**(-1.5))


def all_spin_window():
    from math import atan
    cone=.1
    e_low,e_high=.95,1.15
    exposure=cone**2*(atan(5)-atan(3))/(e_high*(1+.004))
    beta_min=sqrt(1-(21/26)/e_low**2)
    beta_max=sqrt(1-.4/e_high**2)
    ratio=2*(1+beta_max)/(1+.98*beta_min)
    assert ratio<2.8
    theta=(cone*sqrt(2)/e_low)*(1/1.5-1/5)/sqrt(1-2*cone**2/(e_low**2*1.5**2))
    lateral=6.5*theta
    lead=1.5*(1-cone**2)/(2*e_high**2)
    assert lead>lateral
    sample=thermal_source(4*pi*(5e-5)**2,300.,.1,10.)
    schwarz_exposure=sample["early_seconds"]/(sample["radius_m"]/c)
    count=sample["mean_absorbed"]*exposure/schwarz_exposure
    upper=2*2.8*sqrt(pi*(1+4/expm1(1))/(2*count))
    return dict(exposure_in_2M=exposure, spectral_ratio=ratio, uniform_ratio_used=2.8,
                maximal_transverse_angle=theta, relay_in_rplus=lateral, lead_in_rplus=lead,
                time_left_in_rplus=lead-lateral,minimum_photons_grain_10_solar=count,
                maximum_radial_grain_10_solar=upper, min_solar_for_one_percent=10*(upper/.01)**2)


def precursor(mass, length, solar_masses):
    # A causal exterior edge reads only an early part of the falling stress pulse.
    R = 2*G*1.98847e30*solar_masses/c**2
    x=1.05
    beta=1/sqrt(x)
    duration=length/(beta*c)
    clock=duration/4
    jitter=.01*duration
    compton_time=hbar/(mass*c*c)
    advance=R/c*quad(lambda r:1/((1/sqrt(r))*(1+1/sqrt(r))),1,x)[0]
    lateral=length/(c*sqrt(1-1/x))
    free_time=1e-7  # proper time of free center-of-mass motion before the edge
    spread_x=sqrt(hbar*free_time/mass)
    spread_t=spread_x/(beta*c)
    seed_time=duration/8
    k=mass*c*c*spread_t/(hbar*duration)
    gaussian_return=min(1.,sqrt(pi)/(k*seed_time))
    # Analytic Gaussian integral for the clock, avoiding fast oscillations.
    from scipy.special import erf
    y=k*seed_time
    exact=sqrt(pi)*erf(y)/y+np.expm1(-y*y)/y**2
    assert exact<=gaussian_return and spread_t<duration/128
    return dict(mass_kg=mass, length_m=length,pulse_s=duration, gate_s=clock,
                free_time_s=free_time,minimum_position_spread_m=spread_x,
                minimum_timing_spread_s=spread_t,gaussian_clock_purity_bound=gaussian_return,
                inverse_purity_lower=1/gaussian_return, finite_256_gaussian_bound=float(np.nextafter(1/256+gaussian_return,float('inf'))),
                timing_support_s=jitter, radial_upper=min(1.,2*pi*compton_time*duration/(jitter*clock)),
                early_advantage_s=advance,lateral_light_s=lateral,
                remaining_s=advance-lateral-.75*duration)


def relative_circle(warm_cases, cold_cases):
    """Relative angular recoil, spectral coverage and the cost of genuine KK momentum."""
    from math import cos, exp, log, sin
    from scipy.linalg import eigh_tridiagonal
    from scipy.special import jv

    def circular_bound(small):
        small = min(1., small)
        return small*(1.-log(small))

    errors = []
    for kick in (0., .17, 2.4, 19., 40.):
        angles = 2*pi*np.arange(2048)/2048
        modes = np.arange(-128,129)
        amplitudes = np.fft.fft(np.exp(-1j*kick*np.cos(angles)))/len(angles)
        expected = (-1j)**modes*jv(modes,kick)
        errors.append(float(np.max(np.abs(amplitudes[modes]-expected))))
        assert abs(sum(abs(expected)**2)-1)<2e-13
        assert abs(sum(modes**2*abs(expected)**2)-kick**2/2)<2e-10
    assert max(errors)<2e-13

    # Evolution in the neutral |n,-n> sector with a genuine pair energy k|n|.
    # Removing the global phase gives the nearest-neighbour matrix with off-diagonal z/2.
    recoil_checks=[]
    modes=np.arange(-48,49)
    for kick,gap in ((.6,.04),(3.,.01),(8.,.02),(3.,.3)):
        energies,states=eigh_tridiagonal(gap*np.abs(modes),np.full(len(modes)-1,kick/2))
        vector=states@(np.exp(-1j*energies)*states[len(modes)//2,:])
        flat=(-1j)**modes*jv(modes,kick)
        distance=float(np.linalg.norm(vector-flat))
        ceiling=gap*kick/(2*sqrt(2))
        assert distance<=ceiling+1e-13
        recoil_checks.append([kick,gap,distance,ceiling])

    # Per-ray Planck lower density and elementary bounds on the continuous band.
    band=quad(lambda y:y*y/expm1(y),1.,2.)[0]
    floor=1/expm1(2.)
    nmax=1/expm1(1.)
    coverage=floor*.1*(1-cos(1.))/band
    damping=coverage/(1+4*nmax)
    for u in np.geomspace(1.,500.,512):
        assert 1-(sin(2*u)-sin(u))/u>=.1*(1-cos(1.))
    for x in (.75,2.,10.,100.):
        def integrate_v(angle):
            from scipy.special import i0e
            return i0e((x*sin(angle))**2/2)
        angular=2/pi*quad(integrate_v,0,pi/2,epsabs=1e-12)[0]
        assert angular<=circular_bound(sqrt(pi)/(2*x))+1e-13

    warm=[]
    for case in warm_cases:
        scale=case["gate_min_asymptotic_s"]
        count=case["mean_absorbed"]
        at_first=circular_bound(case["constant"]/(4*sqrt(count)))
        late=circular_bound(case["constant"]/(4*sqrt(count))*scale/1e-8)
        rms=3.2*Boltzmann*case["temperature_K"]*sqrt((1+nmax)*count)
        # Sufficient impulse condition for p<.01, not a measurement of a circle radius.
        allowance=.1-sqrt(at_first)
        gap=4*sqrt(2)*hbar**2*max(0.,allowance)/(rms*scale**2)
        lapse=sqrt(1-1/1.05)
        warm.append(dict(body=case["body"],solar=case["black_hole_solar_masses"],
                         radial_at_first=at_first,radial_at_10ns=min(1.,late+exp(-damping*count)),
                         damping_exponent=damping*count,
                         max_frequency_error_at_10ns=coverage/(2e-8),
                         rms_energy_ceiling_J=rms,sufficient_pair_gap_J=gap,
                         sufficient_radius_m=2*lapse*hbar*c/gap if gap>0 else None))
    cold=[dict(mass_kg=row["mass_kg"],circle_seed_purity=circular_bound(row["gaussian_clock_purity_bound"]/2))
          for row in cold_cases]
    return dict(warm=warm,cold=cold,maximum_fft_error=max(errors),finite_gap_checks=recoil_checks,
                band_area=band,continuum_damping_per_count=damping)


def positive_momentum_blocks(warm_cases, cold_cases, damping):
    """Finite fixed-total momentum; both separated blocks retain at least one unit."""
    from math import exp, sin
    from scipy.linalg import eigh_tridiagonal
    from scipy.constants import elementary_charge

    checks=[]
    for q in (2,4,9,16,32):
        dim=2*q-1
        roots,states=eigh_tridiagonal(np.zeros(dim),np.full(dim-1,.5))
        angles=pi*(np.arange(q)+.5)/q
        nodes=(1+np.cos(angles))/2
        center=states[q-1]**2
        # Return amplitude from direct diagonalization vs the q equally weighted modes.
        err=0.
        for strength in (.25,2.,13.,45.):
            measured=np.dot(center,np.exp(-1j*strength*(1+roots)/2))
            expected=np.mean(np.exp(-1j*strength*nodes))
            err=max(err,float(abs(measured-expected)))
        assert err<2e-13
        min_sep=sin(pi/q)*sin(pi/(2*q))
        assert abs(min(abs(np.diff(nodes)))-min_sep)<3e-16
        checks.append([q,err,min_sep])
    q=128
    spacing=sin(pi/q)*sin(pi/(2*q))
    warm=[]
    for row in warm_cases:
        t0=row["gate_min_asymptotic_s"]
        dur=1.e-9
        assert dur*spacing>t0
        # The factor 1/2 permits an occupied-band transport error as in the text.
        log_tail=-damping*row["mean_absorbed"]/2
        # Store a conservative representable value even if the positive tail underflows.
        ceiling=float(np.nextafter(1/q+(1-1/q)*exp(log_tail),float('inf')))
        eps=hbar/dur*max(0.,.1-sqrt(ceiling))
        lapse=sqrt(1-1/1.05)
        warm.append(dict(body=row["body"],solar=row["black_hole_solar_masses"],
                         radial_floor=1/q,radial_ceiling=ceiling,log_offdiag_bound=log_tail,
                         shortest_contact_s=t0/spacing,contact_s=dur,
                         norm_tolerance_eV=eps/elementary_charge,
                         budget_radius_m=2*q*lapse*hbar/(row["mass_kg"]*c)))
    cold=[]
    for row in cold_cases:
        y=sqrt(pi)/row["gaussian_clock_purity_bound"]*spacing
        cold.append(dict(mass_kg=row["mass_kg"],log_offdiag_bound=-y*y,
                         purity_bound=float(np.nextafter(1/q+(1-1/q)*exp(-y*y),float('inf')))))
    return dict(q=q,total_positive_units=2*q,minimum_q_for_below_one_percent=101,
                minimum_weighted_delay_spacing=spacing,warm=warm,cold=cold,
                path_spectrum_checks=checks)


def main():
    opts=[]
    for solar in (3.,10.,1.e6):
        for name,area,mass in [("warm person",1.7,70.),
                               ("1 mm diameter",4*pi*(5.e-4)**2,4*pi*(5.e-4)**3*2500/3),
                               ("0.1 mm diameter",4*pi*(5.e-5)**2,4*pi*(5.e-5)**3*2500/3)]:
            opts.append(dict(body=name,mass_kg=mass,**thermal_source(area,300.,.1,solar)))
    cold=thermal_source(4*pi*(5.e-5)**2,30.,.01,10.)
    patch=[local_patch(a,300.,.1) for a in (5e-5,5e-4,.1)]
    result=dict(cases=opts,cold_small=cold,local_patches=patch,clock_checks=common_clock(),
                all_subextremal_axial=all_spin_window(),
                active_body_tide=elastic_and_direct(10.,70.),
                precursor=[precursor(70.,1.7,10.), precursor(4*pi*2500*(5e-5)**3/3,1e-4,10.)])
    result["relative_circle"]=relative_circle(opts,result["precursor"])
    result["positive_momentum_blocks"]=positive_momentum_blocks(
        opts,result["precursor"],result["relative_circle"]["continuum_damping_per_count"])
    assert opts[5]["radial_upper"]<.01 and opts[0]["radial_upper"]<2e-6
    (ROOT/"verification"/"visible-body-flux-results.json").write_text(
        json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf8")
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    radii=np.geomspace(20e-6,1e-3,180)
    fig,ax=plt.subplots(figsize=(6.5,2.9),layout="constrained")
    for ix,colour in [(2,"#83576d"),(5,"#136867"),(8,"#86651e")]:
        row=opts[ix]
        scaled=np.minimum(1.,row["radial_upper"]*5e-5/radii)
        ax.loglog(2e3*radii,scaled,color=colour,label=f'{row["black_hole_solar_masses"]:g} solar masses')
    ax.axhline(.01,ls=":",lw=1,color="0.35")
    ax.set(xlabel="Diameter of warm sphere (mm)",ylabel="Upper bound on radial fraction")
    ax.legend(frameon=False,ncol=3,fontsize=8)
    (ROOT/"manuscripts").mkdir(exist_ok=True)
    fig.savefig(ROOT/"manuscripts"/"visible_body_flux.pdf",metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)
    print([(p["body"],p["mean_absorbed"],p["radial_upper"]) for p in opts[3:6]])
    print(patch)


if __name__=="__main__":
    main()
