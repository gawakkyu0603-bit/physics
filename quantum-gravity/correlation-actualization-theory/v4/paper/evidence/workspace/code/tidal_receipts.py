"""Gravitational receipts from a weak hyperbolic encounter and a fluid's Kelvin mode."""
from fractions import Fraction
from math import exp, log, pi, sqrt
from pathlib import Path
import json

import numpy as np
from scipy.constants import G, c, hbar, k as boltzmann, parsec
from scipy.integrate import quad, solve_ivp
from scipy.linalg import expm
from scipy.optimize import brentq
from scipy.special import kv, ive, gammaln

ROOT = Path(__file__).resolve().parents[1]
EYE = np.eye(3)
ALONG = np.array([0., 1., 0.])
NORMAL = np.array([0., 0., 1.])


def tt(tensor, direction=NORMAL):
    screen = EYE - np.outer(direction, direction)
    return screen @ tensor @ screen - screen * np.trace(screen @ tensor) / 2


def kelvin_shape(u):
    r = np.array([1.,u,0.])
    square = 1+u*u
    return (3*np.outer(r,r)/square-EYE)/square**1.5


def orbital_jerk(u):
    r = np.array([1.,u,0.])
    sym = (np.outer(r,ALONG)+np.outer(ALONG,r))/2
    tensor = 4*sym/(1+u*u)**1.5 - 3*u*np.outer(r,r)/(1+u*u)**2.5
    return tensor-EYE*np.trace(tensor)/3


def spectra(x):
    """Transform at positive x=omega*b/v with the convention exp(+i*x*u)."""
    k0, k1 = kv(0,x), kv(1,x)
    a = 2*x*k1
    near = np.diag([2*x*x*k0+a,-2*x*x*k0,-a]).astype(complex)
    near[0,1] = near[1,0] = 1j*x*a
    plus = -1j*x*(a+k0)
    cross = a+2*x*x*k0
    wave = np.array([[plus,cross,0],[cross,-plus,0],[0,0,0]],complex)
    return near,wave


def transform_check(x, profile):
    out = np.zeros((3,3),complex)
    for i,j in [(0,0),(1,1),(2,2),(0,1)]:
        fn = lambda u: profile(u)[i,j]
        re = quad(lambda u:fn(u)+fn(-u), 0,np.inf,weight="cos",wvar=x,epsabs=2e-11)[0]
        im = quad(lambda u:fn(u)-fn(-u), 0,np.inf,weight="sin",wvar=x,epsabs=2e-11)[0]
        out[i,j] = out[j,i] = re+1j*im
    return out


def circular(tensor):
    difference = (tensor[0,0]-tensor[1,1])/2
    return np.array([difference-1j*tensor[0,1],difference+1j*tensor[0,1]])


def diffraction_checks():
    checks = []
    for x in [.3,1.,3.]:
        local,wave = spectra(x)
        local_error = np.max(abs(local-transform_check(x,kelvin_shape)))
        wave_error = np.max(abs(wave-tt(transform_check(x,orbital_jerk))))
        assert max(local_error,wave_error)<4e-11
        checks.append([x,float(local_error),float(wave_error)])
    measured = quad(lambda u:np.vdot(orbital_jerk(u),orbital_jerk(u)).real,-np.inf,np.inf)[0]*4/5
    assert abs(measured-37*pi/15)<2e-12
    return dict(spectra=checks,orbital_burst_coefficient=measured)


def cold_edge(plus,minus):
    """P(-1 <= n_plus-n_minus <= 1), from independent Poisson populations."""
    if min(plus,minus)==0:
        mean=max(plus,minus)
        return 0. if mean>740 else (1+mean)*exp(-mean)
    z=2*sqrt(plus*minus)
    return float(exp(-(sqrt(plus)-sqrt(minus))**2) *
                 (ive(0,z)+(sqrt(plus/minus)+sqrt(minus/plus))*ive(1,z)))


def paired_edge(plus,minus,thermal):
    if thermal==0: return cold_edge(plus,minus)
    # Average pure number-difference-zero squeezed states over their physically absent pair phase.
    def prob(phi):
        a=sqrt(thermal+1)*sqrt(plus)-np.exp(1j*phi)*sqrt(thermal)*sqrt(minus)
        b=sqrt(thermal+1)*sqrt(minus)-np.exp(1j*phi)*sqrt(thermal)*sqrt(plus)
        return cold_edge(abs(a)**2,abs(b)**2)
    return quad(prob,0,pi,epsabs=1e-11)[0]/pi


def work_distribution():
    # Check the phase average against displacement of diagonal paired Fock states, independently.
    nmax=22
    annihilate=np.diag(np.sqrt(np.arange(1,nmax)),1)
    mu_p,mu_m,thermal=.7,.18,.35
    probabilities=[]
    for intensity in [mu_p,mu_m]:
        disp=expm(sqrt(intensity)*(annihilate.T-annihilate))
        probabilities.append(abs(disp)**2)
    q=thermal/(1+thermal)
    joint=(probabilities[0]*((1-q)*q**np.arange(nmax)))@probabilities[1].T
    delta=np.arange(nmax)[:,None]-np.arange(nmax)
    edge=joint[abs(delta)<=1].sum()
    assert abs(edge-paired_edge(mu_p,mu_m,thermal))<3e-10
    mean=(joint*delta).sum()
    var=(joint*(delta-mean)**2).sum()
    assert abs(mean-mu_p+mu_m)<5e-8 and abs(var-(2*thermal+1)*(mu_p+mu_m))<5e-7
    return dict(explicit_edge=float(edge),mean=float(mean),variance=float(var))


def loss_without_source():
    # An initially neutral pair, with each excitation surviving in its original mode with probability u.
    def silent_boundary(a):
        root=sqrt(1+4*a)
        ratio=2*a/(1+2*a+root)
        return (1+2*ratio)/root
    mean=2.
    u=.65
    a=mean*u*(1-u)
    result=silent_boundary(a)
    fourier=quad(lambda t:(1+2*np.cos(t))/(1+2*a*(1-np.cos(t))),0,pi)[0]/pi
    assert abs(fourier-result)<1e-12
    threshold=brentq(lambda z:silent_boundary(z)-.99,0.,1.)
    return dict(test_boundary=result,maximum_noise_for_99=threshold)


def power_profile_receipts():
    # Circular components of the STF Hessian of an inverse-power interaction.
    rows=[]
    for power in [1,7]:
        nu=(power+3)/2
        def transform(x):
            return 2*sqrt(pi)*exp(-gammaln((power+4)/2))*(x/2)**nu*kv(nu,x)
        def derivative(x):
            coeff=2*sqrt(pi)*exp(-gammaln((power+4)/2))/2**nu
            d=-coeff*x**nu*kv(nu-1,x)
            dd=coeff*(x**nu*kv(nu-2,x)-x**(nu-1)*kv(nu-1,x))
            return d,dd
        x=1.
        d,dd=derivative(x)
        strengths=[(transform(x)+sgn*2*d+dd)**2 for sgn in [-1,1]]
        def direct(sign):
            f=lambda u: (1+sign*1j*u)**2/(1+u*u)**((power+4)/2)
            re=quad(lambda u:2*f(u).real,0,np.inf,weight='cos',wvar=x)[0]
            im=quad(lambda u:2*f(u).imag,0,np.inf,weight='sin',wvar=x)[0]
            return (re-im)**2
        assert np.max(abs(np.array(strengths)-[direct(-1),direct(1)]))<2e-8
        rows.append(dict(power=power,counter_to_corotating=strengths[1]/strengths[0]))
    return rows


def root_distance(intensities,temperature):
    # Reference distance is one parsec; each mean occupation scales as inverse distance squared.
    return exp(brentq(lambda d:paired_edge(*(intensities/exp(2*d)),temperature)-.99,
                      log(1e-3),log(1e14)))


def encounter():
    radius=1.e6
    density=5000.
    mass=4*pi*density*radius**3/3
    inertia=mass*radius**2/5
    omega=sqrt(4*G*mass/(5*radius**3))
    impact=25*radius
    speed=impact*omega
    perturber=mass
    source=G*perturber/(impact**2*speed)
    wave=2*G**2*mass*perturber*omega/(c**4*impact*parsec)
    normal=sqrt(inertia/(2*hbar*omega))
    tides,jerk=spectra(1.)
    local=normal*circular(tides)*source
    distant=normal*circular(1j*jerk)*wave
    all_near=normal*tides*source
    lum=37*pi/15*G**3*mass**2*perturber**2*speed/(c**5*impact**3)
    orbital_energy=mass*perturber/(mass+perturber)*speed**2/2
    mode_energy=float(np.vdot(all_near,all_near).real*hbar*omega)
    near_intensity=abs(local)**2
    far_base=abs(distant)**2
    gamma_g=4*G*inertia*omega**4/(5*c**5)
    cold_threshold=root_distance(far_base,0.)
    hot_mean=1/np.expm1(hbar*omega/(3*boltzmann))
    # For large thermal means, evaluating Bessel I_n at huge argument is avoided
    # by bracketing around the scale where the 99 percent criterion can occur.
    def hot_root(nbar):
        scale=cold_threshold*sqrt(1+2*nbar)
        f=lambda y:paired_edge(*(far_base/(y*scale)**2),nbar)-.99
        return scale*brentq(f,.05,20.)
    hot_threshold=hot_root(hot_mean)
    hot_mid=hot_root(10.)
    distances=[cold_threshold,10*cold_threshold,hot_mid,hot_threshold]
    rows=[]
    for distance in distances:
        p,m=far_base/distance**2
        rows.append(dict(pc=distance,lambda_plus=p,lambda_minus=m,
                         cold_boundary=cold_edge(p,m)))
    gamma_visc=10e-6/radius**2
    lag=50/omega
    g_onepc=G*inertia*omega**3/(c**4*parsec)
    assert abs(g_onepc-5*gamma_g/(4*omega*parsec/c))<1e-12*g_onepc
    # Ring forcing following the pulse. All fields share the same retarded observation window.
    return dict(radius_m=radius,density=density,mass_kg=mass,omega_per_s=omega,impact_m=impact,
                speed_m_s=speed,deflection_parameter=G*(mass+perturber)/(impact*speed**2),
                near_intensities=near_intensity.tolist(),one_pc_intensities=far_base.tolist(),
                mode_energy_J=mode_energy,orbital_gw_J=lum,orbital_energy_J=orbital_energy,
                local_strain_norm=sqrt(2*mode_energy/(inertia*omega**2)),
                receipt_cases=rows,cold_boundary_99_pc=cold_threshold,
                thermal_occupation_3K=hot_mean,paired_boundary_99_pc_3K=hot_threshold,
                paired_boundary_99_pc_n10=hot_mid,
                coherent_near_wrong_bound=(sum(near_intensity)/(near_intensity[0]-near_intensity[1]-1)**2),
                gamma_g_per_s=gamma_g,gamma_visc_example_per_s=gamma_visc,g_onepc_per_s=g_onepc,
                short_window_seconds=lag,ring_to_orbit_amplitude=(g_onepc*lag*abs(local/distant)).tolist(),
                hot_unlinked_false_fall=1-(1+3*hot_mean)/(1+hot_mean)/(1+2*hot_mean))


def finite_radiation_waveform(info):
    """Integrate the tide of the orbit and the induced quadrupole of the same fluid body."""
    x_a=1.
    handoff=80.
    eps=1/(5*25**2)
    signs=np.array([-1j,1j])
    def kernel(u,p,s):
        h=1+u*u
        f=(1+signs*u)**p/h**(s/2)
        logd=p*signs/(1+signs*u)-s*u/h
        logdd=-p*signs**2/(1+signs*u)**2-s*(1-u*u)/h**2
        return f,f*logd,f*(logd**2+logdd)
    def values(x_b,start):
        def rhs(u,y):
            y_a,yp_a=y[0:2],y[2:4]
            k,kp,kpp=kernel(u,2,5)
            f,fp,_=kernel(u,1,3)
            tidal=1.5*k
            y4=1.5*kpp-x_a*x_a*(tidal-x_a*x_a*y_a)
            jerk_deriv=2*signs*fp-1.5*(k+u*kp)
            phase=np.exp(1j*x_b*u)
            return np.r_[yp_a,tidal-x_a*x_a*y_a,-jerk_deriv*phase,eps*y4*phase]
        solution=solve_ivp(rhs,(-start,handoff),np.zeros(8,complex),method="DOP853",
                           rtol=3e-11,atol=2e-13)
        assert solution.success
        return solution.y[:,-1]
    # Each normalized Fourier amplitude is converted to a number of received excitations.
    si=info["omega_per_s"]
    far_scale=2*G**2*info["mass_kg"]**2/(c**4*parsec*info["impact_m"])*si
    rows=[]
    def window(freq,elapsed):
        return elapsed*np.sinc(freq*elapsed/(2*pi))*np.exp(1j*freq*elapsed/2)
    for x_b in [1.,1.01]:
        initial=values(x_b,160.)
        repeat=values(x_b,240.)
        assert np.max(abs(initial-repeat)) < 2e-6
        y,yp,prompt,early_ring=repeat.reshape(4,2)
        a_minus=(y+1j*yp/x_a)/2
        a_plus=(y-1j*yp/x_a)/2
        mean_radius=info["radius_m"]
        b_mass=info["mass_kg"]*x_b**2
        factor=sqrt(b_mass*mean_radius**2/(10*hbar*x_b*si))*far_scale
        expected=circular(1j*x_b*spectra(x_b)[1])
        assert np.max(abs(prompt-expected))<4e-4
        detuned_max=0
        when=[]
        for seconds in [handoff/si, 365.25*86400,10*365.25*86400]:
            length=max(0.,si*seconds-handoff)
            tail=eps*x_a**4*np.exp(1j*x_b*handoff)*(
                a_minus*window(x_b-x_a,length)+a_plus*window(x_b+x_a,length))
            result=factor*(prompt+early_ring+tail)
            means=abs(result)**2
            when.append(dict(post_flyby_seconds=seconds,one_pc_means=means.tolist(),
                             one_pc_cold_edge=cold_edge(*means)))
        if x_b!=x_a:
            # Bounds hold for every later cut in the free ringing approximation.
            amplitude=np.abs(early_ring)+eps*x_a**4*(2*abs(a_minus)/abs(x_b-x_a)+
                                                       2*abs(a_plus)/(x_b+x_a))
            detuned_max=float(np.max(amplitude/np.abs(prompt)))
        rows.append(dict(frequency_ratio=x_b,windows=when,max_detuned_correction=detuned_max,
                         cutoff_convergence=float(np.max(abs(initial-repeat)))))
    return rows


def finite_chart(info,waves):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig,axes=plt.subplots(1,2,figsize=(8,3.05),layout="constrained")
    colors=["#295c88","#b95830","#29776b"]
    distances=np.logspace(-1.2,2.0,120)
    strengths=np.asarray(info["one_pc_intensities"])
    for n,col in zip([0.,1.,10.],colors):
        axes[0].semilogx(distances,[paired_edge(*(strengths/d**2),n) for d in distances],
                         color=col,label=fr"Paired occupation $\bar n={n:g}$")
    axes[0].set(xlabel="Distance to receiver (pc)",ylabel="Horizon-only probability",ylim=(-.025,1.025))
    axes[0].legend(fontsize=7,loc="lower right")
    for row,col,marker in zip(waves,colors,["o","s"]):
        coords=np.array([[v["post_flyby_seconds"]/86400,v["one_pc_cold_edge"]] for v in row["windows"]])
        axes[1].scatter(coords[:,0],coords[:,1],s=30,color=col,marker=marker,
                        label=fr"$\omega_B/\omega_A={row['frequency_ratio']:g}$")
    axes[1].set(xscale="log",xlabel="Received duration after passage (days)",
                ylabel="Horizon-only probability at 1 pc",ylim=(-.025,1.025))
    axes[1].legend(fontsize=7,loc="center left")
    for ax in axes: ax.spines[["right","top"]].set_visible(False)
    fig.savefig(ROOT/"manuscripts"/"tidal_receipts.pdf",metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)


def connected_recoil(info):
    mass=info["mass_kg"]
    reduced=mass/2
    impact=info["impact_m"]
    speed=info["speed_m_s"]
    angular=reduced*impact*speed
    q1=2*hbar*(info["near_intensities"][0]-info["near_intensities"][1])
    q2=q1
    geometric=quad(lambda u:1/(1+u*u),0,1)[0]
    phase_coeff=4*hbar*geometric/angular
    force=2*q1*q2/(reduced*impact**3)
    # Verify the finite difference at a smaller dynamic range than the astronomical example.
    energy=lambda l:l*l/(2*Fraction(17,5))
    l,a,b=Fraction(43,7),Fraction(3,5),Fraction(-2,9)
    assert energy(l-a-b)-energy(l-a)-energy(l-b)+energy(l)==a*b/Fraction(17,5)
    return dict(quarter_turn_phase_per_kk=phase_coeff,orbital_L_over_hbar=angular/hbar,
                source_charge_over_orbital=q1/angular,
                connected_force_over_newton=force/(G*mass**2/impact**2))


def information_at_capture(info):
    """Distinguish two mirror orbits from a received signed tidal charge."""
    from scipy.stats import skellam
    probabilities = {}
    for name, (co, counter) in (("near", info["near_intensities"]),
                                ("far_prompt", info["one_pc_intensities"])):
        odds_per_unit = co / counter
        entry = {"likelihood_odds_per_unit": odds_per_unit,
                 "orientation_error_at_two": 1 / (1 + odds_per_unit**2)}
        if name == "far_prompt":
            for charge in range(1, 6):
                odds = skellam.pmf(charge, co, counter) / skellam.pmf(-charge, co, counter)
                assert np.isclose(odds, odds_per_unit**charge, rtol=1e-12)
            entry["zero_probability"] = skellam.pmf(0, co, counter)
            entry["orientation_bayes_error_all_charges"] = (
                skellam.cdf(-1, co, counter) + .5 * entry["zero_probability"])
        probabilities[name] = entry
    return probabilities


def boundary_release(info):
    """Ideal polarization-preserving, vacuum release and a competing ordinary loss."""
    width = info["gamma_g_per_s"]
    loss = info["gamma_visc_example_per_s"]
    time99 = -log(.01) / width
    escape = width / (width + loss)
    assert np.isclose(-np.expm1(-width * time99), .99)
    return {"clean_vacuum_99_seconds": time99,
            "clean_vacuum_99_julian_years": time99 / (365.25*86400),
            "untracked_viscosity_gravity_fraction": escape}


def thermal_transfer(info):
    """Check survival of reference entanglement in two placements of Hawking noise."""
    occupation = 1 / np.expm1(1.)
    spectra = []
    for share in (.20, .50, .80):
        for greybody in (.04, 1.):
            for empty_thermal in (False, True):
                eta = greybody * share
                n0 = greybody * occupation * (1 if empty_thermal else 1 - share)
                a = np.cosh(1.4)
                b = eta*a + 1-eta + 2*n0
                corr = sqrt(eta*(a*a-1))
                symplectic_after_pt = np.linalg.eigvalsh([[a,corr],[corr,b]])[0]
                assert (symplectic_after_pt < 1) == (n0 < eta)
                spectra.append([share, greybody, empty_thermal, float(symplectic_after_pt)])
    w = info["gamma_g_per_s"] / (info["gamma_g_per_s"] + info["gamma_visc_example_per_s"])
    return {"energy_ratio_above_for_viscous_material": -log(w),
            "required_share_at_thermal_frequency": exp(-1),
            "required_share_if_empty_flux_is_fixed": occupation,
            "minimum_energy_ratio_if_empty_flux_is_fixed": log(2.),
            "pt_test_cases": spectra}


def infall_thermal_match():
    """Retarded radial deformation at crossing, with no free ringing at past infinity."""
    barrier=(9+sqrt(17))/8
    lapse=sqrt(1-1/barrier)
    def deformation(x):
        a=2*x/3
        return (4/9)*quad(lambda z:z*exp(-z)/(a*a+z*z),0,np.inf,epsabs=3e-13)[0]
    for x in [.2,1.,3.,10.]:
        a=2*x/3
        sine=(4/9)*quad(lambda z:1/(a+z)**2,0,np.inf,weight="sin",wvar=1.,epsabs=1e-12)[0]
        assert abs(deformation(x)-sine)<1e-12
    rows=[]
    for strain in [.1,.03,.01]:
        x=brentq(lambda x:deformation(x)-strain,.01,30.)
        y=4*pi*lapse*x
        z=1/(4*pi*x)
        rows.append(dict(maximum_strain=strain,minimum_fluid_frequency_R_over_c=x,
                         peak_clock_energy_over_kT=y,peak_clock_thermal_occupation=1/np.expm1(y),
                         maximum_clock_ratio_for_y1=z,last_radial_radius_over_R=1/(1-z)**2))
    return dict(peak_lapse=lapse,strain_thresholds=rows)


def radial_material_receipt(info):
    """Spherical infall, using a local fluid cell and a static exterior reference."""
    inertia = info["mass_kg"] * info["radius_m"]**2 / 5
    scale = 3 * inertia * info["omega_per_s"] / (4 * hbar)

    def quadratures(a):
        options = {"epsabs": 3e-14, "epsrel": 1e-12}
        deformation = (4/9) * quad(lambda z: z*exp(-z)/(a*a+z*z), 0, np.inf, **options)[0]
        speed = (4/9) * quad(lambda z: z*z*exp(-z)/(a*(a*a+z*z)), 0, np.inf, **options)[0]
        equilibrium = 4 / (9*a*a)
        # A derivative and a Fourier integral use the original retarded coordinate.
        step = 2e-5*a
        def original(t):
            return (4/9)*quad(lambda z: 1/(z+t)**2, 0, np.inf, weight="sin", wvar=1., **options)[0]
        finite_difference = (original(a-step)-original(a+step)) / (2*step)
        assert abs(finite_difference-speed) < 2e-8*speed
        return np.array([deformation, speed]), equilibrium

    rows = []
    for x in (3., 10.):
        hquad, eq = quadratures(2*x/3)
        q15, _ = quadratures((2*x/3)*1.5**1.5)
        lag = hquad - [eq, 0.]
        count = scale * np.dot(lag,lag)
        difference = scale * np.sum((hquad-q15)**2)
        rows.append({"X": x, "crossing_strain": hquad[0], "equilibrium_strain": eq,
                     "speed_over_frequency": hquad[1], "mean_relative_quanta": count,
                     "log10_probability_horizon": (np.log1p(count)-count)/log(10),
                     "log10_squared_overlap_two_stages": -difference/log(10)})
    # Pull back a regularized surface delta along the inward geodesic.
    # F=1-R/r, tau in R/c units, so abs(dF/dtau)*abs(dtau/dr)=1/r**2 (R=1).
    widths = [.04,.02,.01]
    normalizations = []
    for width in widths:
        integrand = lambda r: exp(-.5*((1-1/r)/width)**2)/(sqrt(2*pi)*width*r*r)
        norm = quad(integrand,.55,1.,epsabs=1e-12)[0]+quad(integrand,1.,3.,epsabs=1e-12)[0]
        assert abs(norm-1)<1e-11
        normalizations.append(norm)
    n = 10.
    return {"spherical_infall": rows, "surface_flux_norm": normalizations,
            "cold_exterior_probability_boundary": 1.,
            "independent_thermal_boundary_n10": (1+6*n)/(1+n)**6}


def layer_interaction(info):
    """A gravitationally marked pair detunes a two-channel resonance at capture."""
    def gaussian_fall(u):
        return sqrt(2/pi) * quad(lambda z: exp(-.5*(z/u)**2)/(1+z**4), 0, np.inf,
                                  epsabs=1e-13)[0] / u

    gaussian = []
    for u in (.1, 1., 10., 100.):
        fall = gaussian_fall(u)
        assert 1 - fall <= 3*u**4 + 2e-12
        assert fall <= sqrt(pi)/(2*u) + 2e-12
        gaussian.append([u, fall, 1-fall])
    s_matrix_errors=[]
    for g1,g2,detuning in ((.4,.6,.7),(.5,.5,0.),(.5,.5,17.)):
        amp = np.sqrt([g1,g2])
        s = np.eye(2)-1j*np.outer(amp,amp)/(detuning+1j*(g1+g2)/2)
        s_matrix_errors.append(float(np.max(abs(s.conj().T@s-np.eye(2)))))
        assert abs(abs(s[1,0])**2-g1*g2/(detuning**2+((g1+g2)/2)**2))<1e-14
    assert max(s_matrix_errors)<1e-14
    # A Cauchy-distributed incoming packet has halfwidth b in units of the material halfwidth.
    for b,detuning in [(.05,0.),(.3,.8)]:
        direct = quad(lambda t: b/(pi*(t*t+b*b)*(1+(t-detuning)**2)), -np.inf,np.inf)[0]
        assert abs(direct-(1+b)/((1+b)**2+detuning**2))<2e-13

    t = exp(-1.)
    p0 = (1-t)/(1+t)
    endpoint = 37  # The two-sided geometric tail beyond this charge is below 1e-16.
    weights = np.zeros(endpoint**2+1)
    weights[0] = p0
    for j in range(1,endpoint+1):
        weights[j*j] = 2*p0*t**j
    assert abs(weights.sum()-1)<1e-14
    joint = np.array([1.])
    thermal=[]
    for bands in range(1,7):
        joint = np.convolve(joint, weights)
        if bands in (1,6):
            s = np.arange(len(joint), dtype=float)
            for alpha in (1.,10.,100.):
                fall = float(np.dot(joint, 1/(1+(alpha*s)**2)))
                assert fall+1e-13>=p0**bands
                thermal.append([bands,alpha,fall,1-fall,p0**bands])
    I = info["mass_kg"]*info["radius_m"]**2/5
    omega = info["omega_per_s"]
    gamma = info["gamma_g_per_s"]
    rotor = 4*hbar/(I*gamma)
    bandwidth_noise = (1/np.expm1(1.))
    # Two ways of preparing a second physical carrier from the same wide first marginal.
    # Identity transport locks the charge. A local charge exchange can reload it from matter.
    numbers=np.arange(32)
    marg=t**numbers * (1-t) / (1-t**32)
    marked_difference=(numbers[:,None]-numbers[None,:])**2
    fall=1/(1+(100.*marked_difference)**2)
    assert np.isclose(np.sum(marg*np.diag(fall)),1.)
    assert abs(np.sum((marg[:,None]*marg[None,:])*fall)-thermal[2][2])<5e-13
    return {"gaussian":gaussian, "scattering_unitarity_error":max(s_matrix_errors),
            "thermal_routing":thermal, "B_horizon_ceiling_one_band":1-p0,
            "B_horizon_ceiling_six_bands":1-p0**6,
            "one_band_y_for_99":2*np.arctanh(.01),
            "one_band_w_for_entanglement_at_99":(1-.01)/(1+.01),
            "fluid_quantum_shift_over_halfwidth":rotor,
            "reference_bandwidth_for_99_per_second":gamma/198,
            "resolved_rotor_energy_over_material_gap":2*hbar/(I*omega),
            "thermal_mean_example":bandwidth_noise}


def closed_falling_channel():
    """Fixed total charge of two physically written bosonic modes at a radial threshold."""
    from math import comb
    rows = []
    for n in (100, 101):
        k = np.arange(n+1)
        weights = np.array([comb(n,int(j))/2**n for j in k],dtype=float)
        delta = 2*k-n
        relative_energy = delta**2  # Unit D_min = (one charge quantum)^2/(2I).
        incident = .75
        speed_ratio = np.sqrt(np.maximum(1-relative_energy/incident,0))
        transmission = 4*speed_ratio/(1+speed_ratio)**2
        fell = float(np.dot(weights,transmission))
        assert np.isclose(weights.sum(), 1.)
        assert np.isclose(np.dot(weights,(k-n/2)**2),n/4)
        assert np.isclose(fell, 0. if n%2 else comb(n,n//2)/2**n)
        rows.append({"total":n,"single_layer_variance_in_quanta":n/4,
                     "probability_fall":fell,"probability_boundary":1-fell})
    return rows


def sampled_material_clock():
    # A narrow material tube of constant cross section in a continuum embedding.
    # Poisson quadrature has one intensity unit per u=t/t_b (then divide by that intensity).
    base=circular(spectra(1.)[0])
    noise=27*pi/32
    direct=quad(lambda u:(9/4)/(1+u*u)**3,-np.inf,np.inf)[0]
    assert abs(direct-noise)<2e-12
    rows=[]
    for spacing in [2.,1.,.5,.25]:
        # Symmetric periodic sampling, with both tails bounded using the decaying envelope.
        u=np.arange(-3000,3001)*spacing
        phase=np.exp(1j*u)
        answer=np.array([spacing*np.sum(1.5*(1+s*1j*u)**2/(1+u*u)**2.5*phase) for s in [-1,1]])
        rows.append([spacing,*np.abs(answer-base).tolist()])
    assert max(rows[-1][1:])<2e-8
    # Independent Poisson cell draws on the same tube test the predicted extra second moment.
    rng=np.random.default_rng(115)
    u=(np.arange(600)+.5)*.04-12
    g=1.5*(1-1j*u)**2/(1+u*u)**2.5*np.exp(1j*u)
    intensity=8.
    mean=.04*np.sum(g)
    total=0.
    for _ in range(40):
        counts=rng.poisson(intensity*.04,size=(100,len(u)))
        deviations=np.sum(counts*g,axis=1)/intensity-mean
        total+=np.vdot(deviations,deviations).real
    sampled=total/4000
    predicted=.04*np.sum(abs(g)**2)/intensity
    assert abs(sampled/predicted-1)<.05
    return dict(noise_coefficient=noise,one_percent_mean_occupation_density=(noise/(.01*abs(base)**2)).tolist(),
                uniform_errors=rows,stochastic_variance=float(sampled),finite_tube_variance=predicted)


def horizon_timing():
    def tortoise(x): return x+np.log(x-1)
    def fall(x):
        return quad(lambda u:u/(sqrt(u)+1),1,x)[0]
    rows=[]
    for x in [1.1,1.5,3.,10.,100.]:
        target=tortoise(x)+fall(x)/2
        # Invert without exp overflow in cases of very large radius.
        outer=brentq(lambda z:tortoise(z)-target,1+1e-12,max(3.,target+20))
        assert abs(2*(tortoise(outer)-tortoise(x))-fall(x))<3e-10
        rows.append([x,fall(x),outer])
    return rows


def main():
    info=encounter()
    waves=finite_radiation_waveform(info)
    finite_chart(info,waves)
    values=dict(encounter=info,finite_waveforms=waves,fourier=diffraction_checks(),paired=work_distribution(),
                inverse_power=power_profile_receipts(),round_trip=horizon_timing(),recoil=connected_recoil(info),unassisted_loss=loss_without_source(),infall_match=infall_thermal_match(),material_clock=sampled_material_clock(),
                capture_information=information_at_capture(info),boundary_release=boundary_release(info),
                thermal_transfer=thermal_transfer(info),
                radial_material=radial_material_receipt(info),
                layer_resonance=layer_interaction(info), parity_threshold=closed_falling_channel())
    target=ROOT/"verification"/"tidal-receipts-results.json"
    target.write_text(json.dumps(values,indent=2,allow_nan=False)+"\n",encoding="utf8")
    print("Tidal and radiative spectra, paired thermal counts and receipt probabilities verified.")


if __name__=="__main__":
    main()
