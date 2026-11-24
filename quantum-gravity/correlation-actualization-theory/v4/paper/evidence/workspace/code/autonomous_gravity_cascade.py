"""Appendix P. Ordered photon/graviton delays, Coulomb response and a stopped mediator."""
from fractions import Fraction
from pathlib import Path
import json
import math

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import expm
from scipy.special import ive, jv, kv
from causal_gravity_receiver import radial_sq

ROOT = Path(__file__).resolve().parents[1]


def delay_gram(poles, duration=None):
    poles = np.asarray(poles)
    damping = poles.conjugate()[:, None] + poles[None, :]
    weights = np.sqrt(2*poles.real)
    kernel = 1/damping if duration is None else -np.expm1(-duration*damping)/damping
    return np.outer(weights, weights)*kernel


def target_product(target, competitors):
    a = np.asarray(competitors)
    return float(np.exp(np.log(np.abs((target-a)/(target+a.conjugate()))**2).sum()))


def cascades():
    width, splitting = 1., .65
    poles = width/2 + 1j*np.array([-splitting/2, splitting/2])
    readings = []
    for exposure in (.04, .5, 1., 4., 12.):
        gram = delay_gram(poles, exposure)
        early = -math.expm1(-width*exposure)
        exact = early-width*abs(np.expm1(-(width+1j*splitting)*exposure))/math.hypot(width,splitting)
        assert abs(np.linalg.eigvalsh(gram)[0]-exact)<2e-15
        readings.append([exposure,early,exact])
    gram = delay_gram(poles)
    perfect_clock = 1-width/math.hypot(width,splitting)
    assert abs(np.linalg.eigvalsh(gram)[0]-perfect_clock)<2e-15
    # Independently integrate the overlap of the ordered cascade. A common parent
    # linewidth changes only its total-energy envelope, for each relative state.
    for parent_width in (.31, 2.7):
        parent_norm = quad(lambda t:parent_width*np.exp(-parent_width*t),0,np.inf)[0]
        relative_re = quad(lambda t:width*np.exp(-width*t)*np.cos(splitting*t),0,np.inf)[0]
        relative_im = quad(lambda t:width*np.exp(-width*t)*np.sin(splitting*t),0,np.inf)[0]
        assert abs(parent_norm*abs(complex(relative_re,relative_im))-(1-perfect_clock))<2e-12
    weights = np.array([.5, .73, .81, .34])
    frequencies = np.array([-.96, .25, 1.48, 2.67])
    several = weights/2+1j*frequencies
    full = delay_gram(several)
    target_results = []
    for j in range(len(several)):
        success = target_product(several[j],np.delete(several,j))
        assert abs(success-1/np.linalg.inv(full)[j,j].real)<2e-14
        target_results.append(success)
    # Confluent limit: finite-cutoff Cauchy product for a fixed target.
    r = .37
    floor = (math.pi*r/math.sinh(math.pi*r))**2
    high_targets = []
    for n in (4, 12, 50, 200):
        m = np.arange(3,30001,dtype=float)
        def series(k): return r/k**3-1j/k**2
        infinite_approx = target_product(series(float(n)),series(m[m!=n]))
        assert infinite_approx>=floor-1e-12
        high_targets.append([n,infinite_approx])
    return dict(two_packets_full=perfect_clock,early_joint=readings,
                target_specific=target_results,rydberg_radius_ratio=r,
                rydberg_uniform_target_floor=floor,rydberg_cutoff_30000=high_targets)


def bound_strength(n):
    x=1/np.asarray(n,dtype=float)
    return 4096*x**3*(1-4*x*x)/(1-x*x)**7*np.exp(2/x*(np.log1p(-x)-np.log1p(x)))


def continuum_strength(k):
    if k==0:
        return 4096*math.exp(-4)
    return (4096*(1+4*k*k)/(1+k*k)**7*math.exp(-4*math.atan(k)/k)
            /(-math.expm1(-2*math.pi/k)))


def continuum_from_radial_equation(k):
    # Regular energy-normalized Coulomb radial function u=r R in Hartrees.
    # The analytic normalization cancels the exponential in |Gamma(3-i/k)|.
    start=.002
    amplitude=math.sqrt(2/(math.pi*k))*k**3/30*math.sqrt(
        2*math.pi/k*(1+1/k**2)*(4+1/k**2)/(-math.expm1(-2*math.pi/k)))
    powers=[1.,-1/3]
    for degree in range(2,10):
        powers.append(-(2*powers[-1]+k*k*powers[-2])/(degree*(degree+5)))
    u=amplitude*sum(c*start**(d+3) for d,c in enumerate(powers))
    du=amplitude*sum((d+3)*c*start**(d+2) for d,c in enumerate(powers))
    missed=quad(lambda r:2*r**3*math.exp(-r)*amplitude*
                sum(c*r**(d+3) for d,c in enumerate(powers)),0,start)[0]
    def radial_rhs(r,state):
        value,slope,integral=state
        return [slope, -(k*k+2/r-6/r**2)*value, 2*r**3*math.exp(-r)*value]
    integration=solve_ivp(radial_rhs,(start,52),(u,du,missed),rtol=9e-12,
                          atol=3e-15,method="DOP853")
    assert integration.success
    return integration.y[2,-1]**2


def atom():
    f=Fraction
    gap43=(f(1,9)-f(1,16))/2
    gap32=(f(1,4)-f(1,9))/2
    width4=f(4,3)*gap43**3*f(3,7)*radial_sq(4,3,3,2,1)
    width3=f(4,3)*gap32**3*f(2,5)*radial_sq(3,2,2,1,1)
    g3=f(4,75)*f(4,9)**5*radial_sq(3,2,1,0,2)
    assert g3==f(1,360)
    bound_checks=[]
    for n in range(3,11):
        independent=float(radial_sq(n,2,1,0,2))
        assert abs(independent/bound_strength(n)-1)<1e-13
        bound_checks.append([n,float(bound_strength(n))])
    continuum_checks=[]
    for k in (.025,.17,.6,1.4):
        radial=continuum_from_radial_equation(k)
        exact=continuum_strength(k)
        assert abs(radial/exact-1)<2e-9
        continuum_checks.append([k,exact,radial])
    threshold_by_bessel=quad(lambda r:2*r**4*math.exp(-r)*math.sqrt(2/r)*
                             jv(5,2*math.sqrt(2*r)),0,90,epsabs=3e-12)[0]**2
    assert abs(threshold_by_bessel/continuum_strength(0)-1)<5e-13
    return dict(width_4f_in_mu_alpha5=str(width4),width_3d_in_mu_alpha5=str(width3),
                branching_gamma_then_graviton_in_G_mu2_alpha=float(g3/width3),
                mean_completion_in_inverse_mu_alpha5=float(1/width4+1/width3),
                bound_radial=bound_checks,continuum_ode=continuum_checks,
                threshold_radial=threshold_by_bessel,
                threshold_gravity_in_G_mu2_alpha4=512/75*math.exp(-4))


def collective():
    b=np.array([.36+.4j,.6+.7j,.2+1.3j])
    row=np.array([.18, .23j, -.34+.12j])
    generator=np.diag(b)+np.outer(row.conjugate(),row)/2
    channels=np.vstack((np.diag(np.sqrt(2*b.real)),row))
    def derivative(t):
        evo=expm(-generator*t)
        return evo.conj().T@channels.conj().T@channels@evo
    T=2.31
    from scipy.integrate import quad_vec
    integrated=quad_vec(derivative,0,T,epsabs=1e-12)[0]
    survival=expm(-generator*T)
    balance=np.linalg.norm(integrated+survival.conj().T@survival-np.eye(3))
    assert balance<2e-13
    for s in (.01+.32j,1.1-.7j):
        direct=row@np.linalg.inv(np.eye(3)*s+generator)
        predicted=row/(s+b)/(1+.5*np.sum(np.abs(row)**2/(s+b)))
        assert np.max(np.abs(direct-predicted))<3e-14
    fractions=[]
    for n in (6,7,8):
        line=np.sqrt(.15)*np.ones(n)
        floor=float(np.linalg.eigvalsh(np.eye(n)-np.outer(line,line))[0])
        assert abs(floor-(1-.15*n))<1e-14
        fractions.append([n,floor])
    return dict(energy_and_probability_balance=float(balance),spectator_matrix_minima=fractions)


def threshold_edges():
    # Compare finite sums at two cutoffs and evaluate the upper continuum using
    # a logarithmically stable subtraction of its exactly constant edge density.
    j0=(512/75)*math.exp(-4)
    cutoff=.5/9
    data=[]
    for sigma in np.geomspace(2e-2,1e-6,11):
        def lower(last):
            n=np.arange(3,last+1,dtype=float)
            delta=.5/n**2
            weight=(4/75)*(.5-delta)**5*bound_strength(n)
            return .5*np.sum(weight/(sigma+.025/n**3-1j*delta)).imag
        def density(u):
            return (4/75)*(.5+u)**5*continuum_strength(math.sqrt(2*u))
        def regular(u): return -(density(u)-j0)*u/(sigma*sigma+u*u)/2
        upper=quad(regular,0,cutoff,epsabs=1e-13)[0]-j0/4*math.log1p((cutoff/sigma)**2)
        bottom=lower(80000)
        assert abs(bottom-lower(40000))<2e-8
        data.append([float(sigma),float(bottom),upper,float(bottom+upper)])
    logstep=math.log(data[-2][0]/data[-1][0])
    lower_slope=(data[-1][1]-data[-2][1])/logstep
    upper_slope=(data[-1][2]-data[-2][2])/logstep
    assert abs(lower_slope/(j0/2)-1)<.001 and abs(upper_slope/(j0/2)+1)<.001
    return dict(lower_expected_slope=j0/2,lower_last_slope=lower_slope,
                upper_last_slope=upper_slope,edge_scan=data)


def stopped_mediator():
    g,j,omega,k=.31,1.,1.2,.72
    u=4*(g*j/omega)**2
    def visible(t):return math.exp(-u*(1-math.cos(omega*t)))
    def energy(t):return 2*omega*(g*j/omega)**2*(1-math.cos(omega*t))
    integrals=[quad(lambda t:k*math.exp(-k*t)*func(t),0,np.inf,epsabs=3e-13)[0]
               for func in (visible,energy)]
    bessel=ive(0,u)+2*sum(ive(m,u)*k*k/(k*k+(m*omega)**2) for m in range(1,26))
    static=2*g*g/omega
    predicted=j*j*static*omega**2/(k*k+omega**2)
    assert abs(bessel-integrals[0])<2e-10 and abs(predicted-integrals[1])<3e-12
    lowering=np.diag(np.sqrt(np.arange(1,24)),1)
    vacuum=np.eye(24)[:,0]
    for t in (.31,2*math.pi/omega):
        states=[expm(-1j*t*(omega*lowering.T@lowering+
                sign*g*j*(lowering+lowering.T)))@vacuum for sign in (-1,1)]
        assert abs(np.vdot(states[0],states[1])-visible(t))<3e-13
        assert abs(omega*np.linalg.norm(lowering@states[0])**2-energy(t))<3e-13
    return dict(omega=omega,ordinary_width=k,gravity_contact=g,static_cross_strength=static,
                direct_equal_square_visibility=1.,mediated_visibility=float(bessel),
                mediated_residual_energy=predicted)


def recoil_resolved_sidebands():
    # Compare both signs by diagonalizing the occupied oscillator independently.
    # The continuum rate has the ordinary E1 and tidal quadrupole frequency powers.
    gap, coupling, width = 1., .37, .24
    number=np.arange(24)
    lowering=np.diag(np.sqrt(number[1:]),1)
    spectra=[np.linalg.eigh(np.diag(number*gap)+sign*coupling*(lowering+lowering.T))
             for sign in (1,-1)]
    cases=[]
    for energy in (.81,1.83,3.08):
        weights=[]
        cross=[]
        for level in range(1+math.floor(energy/gap)):
            available=energy-level*gap
            def amplitude(w,s):
                eig,vec=spectra[s]
                return np.sum(vec[level,:]*vec[0,:]/(.47*energy-w-eig+1j*width/2))
            for test in (.12,.51,.87):
                v1=amplitude(test*available,0)
                v2=amplitude(test*available,1)
                assert abs(v1-(-1)**level*v2)<5e-13
            def joint(w,s):
                return w**3*(available-w)**5*amplitude(w,0)*amplitude(w,s).conjugate()
            weights.append(quad(lambda w:joint(w,0).real,0,available,epsabs=1e-14)[0])
            cross.append(quad(lambda w:joint(w,1).real,0,available,epsabs=1e-14)[0])
        populations=np.array(weights)/sum(weights)
        signed=sum(cross)/sum(weights)
        work=gap*np.dot(np.arange(len(populations)),populations)
        assert abs(signed-(1-2*sum(populations[1::2])))<3e-13
        assert 1-signed<=2*work/gap+2e-12
        if energy<2*gap:
            assert abs(signed-(1-2*work/gap))<3e-13
        cases.append(dict(energy_budget=energy,allowed_probabilities=populations.tolist(),
                          visibility_with_sign=signed,mean_residual_work=work))
    return cases


def microscopic_work():
    # Natural hydrogen clocks and the stable ground-state receiver are separate atoms.
    f=Fraction
    source={2:f(2)}
    first={2:f(1),3:f(2,3)}
    second={2:f(13,12),3:f(13,18),4:f(1,6)}
    def act_radial(poly):
        out={}
        for power,a in poly.items():
            for index,value in ((power-1,power*a),(power-2,f(6-power*(power+1),2)*a)):
                out[index]=out.get(index,f(0))+value
        return {k:v for k,v in out.items() if v}
    def twice_inner(left,right):
        return sum(2*a*b*f(math.factorial(i+j+2),2**(i+j+3))
                   for i,a in left.items() for j,b in right.items())
    assert act_radial(first)==source and act_radial(second)==first
    static=twice_inner(source,first)
    inverse3=twice_inner(first,second)
    assert static==75 and inverse3==f(11995,48)
    n=np.arange(3,20001,dtype=float)
    spacing=(1-1/n**2)/2
    weights=bound_strength(n)
    def spectral_sum(function):
        upper=n[-1]
        tail=continuum_strength(0)*(.5/upper**2-.5/upper**3)*function(.5)
        continuum=quad(lambda k:k*continuum_strength(k)*function((1+k*k)/2),0,np.inf,
                       epsabs=6e-12,epsrel=5e-13)[0]
        return float(np.sum(weights*function(spacing))+tail+continuum)
    measured=[spectral_sum(lambda w:1.),spectral_sum(lambda w:2*w),
              spectral_sum(lambda w:2/w),spectral_sum(lambda w:2/w**3)]
    assert np.allclose(measured,[22.5,30.,75.,float(inverse3)],rtol=3e-12,atol=2e-13)
    widths=[f(4076863488,4747561509943),f(196608,48828125)]
    ratio=(widths[1]/widths[0])**2
    # Subtract the static integrand algebraically, preserving a tiny positive deficit.
    trial_alpha=.08
    deficits=[]
    for width in widths:
        k=float(width)*trial_alpha**3
        d=k*k*spectral_sum(lambda w:2/(w*(w*w+k*k)))
        assert d<=k*k*float(inverse3)*(1+2e-12)
        assert (k*k*float(inverse3)-d)<=k**4*float(inverse3)/(4/9)**2+1e-25
        deficits.append(d)
    assert abs(deficits[1]/deficits[0]/float(ratio)-1)<1e-10
    # Matrix ground-state pair amplitudes from creation operators for heavy/light species.
    # Color copies multiply both positive measures equally and cancel in the normalized response.
    gaps=np.array([2.,1.])
    lines=1/gaps**2
    static_weights=2*lines/gaps
    total=static_weights.sum()
    moment=static_weights@gaps**2
    x,y=1.,4.
    rx,ry=[float(static_weights@(gaps**2/(u+gaps**2))) for u in (x,y)]
    strength_floor=(y-x)*rx*ry/(y*ry-x*rx)
    moment_floor=(y-x)*rx*ry/(rx-ry)
    assert np.allclose([rx/total,ry/total,strength_floor/total,moment_floor/moment],
                       [8/15,7/30,14/15,14/15],rtol=1e-14)
    return dict(hydrogen_moments=measured,inverse_third=str(inverse3),
                fractional_deficit_alpha6=[float(inverse3/static*w*w) for w in widths],
                normalized_deficit_ratio=float(ratio),
                matrix_response_at_one_and_four=[rx/total,ry/total],
                matrix_fraction_of_both_moments=moment_floor/moment)


def compact_membrane_transfer():
    # Time integration of the original inverse-cube image, checked before the Fourier transform.
    for y in (0.,.6,1.9):
        along=quad(lambda t:(1+y*y+t*t)**-3,-np.inf,np.inf,epsabs=2e-13)[0]
        assert abs(along-3*math.pi/(8*(1+y*y)**2.5))<4e-14
    volume=quad(lambda y:(1+y*y)**-2.5,0,np.inf,epsabs=2e-13)[0]
    series=[]
    for impact_ratio in (.18,1.,2.5,6.):
        harmonics=[]
        for charge in (1,2):
            w=charge*impact_ratio
            direct=quad(lambda y:(1+y*y)**-2.5,0,np.inf,weight="cos",wvar=w,
                        epsabs=2e-13,limlst=130)[0]/volume
            proper=quad(lambda t:t*math.exp(-t-w*w/(4*t)),0,np.inf,
                        epsabs=2e-14,epsrel=6e-13)[0]
            analytic=w*w*kv(2,w)/2
            assert math.isclose(direct,analytic,abs_tol=3e-13,rel_tol=2e-10)
            assert math.isclose(proper,analytic,abs_tol=3e-14,rel_tol=2e-11)
            harmonics.append(float(analytic))
        ratio=(harmonics[1]/harmonics[0])**2
        coherence=(ratio-1)/(ratio+1)
        assert 0<ratio<1 and coherence<0
        series.append(dict(impact_over_radius=impact_ratio,harmonics=harmonics,
                           probability_ratio=ratio,signed_coherence=coherence))
    charges=np.arange(-6,7)
    for denominator in (2,3,5):
        angles=np.exp(2j*np.pi*charges/denominator)
        coincident=np.abs(angles[:,None]-angles[None,:])<1e-12
        assert np.array_equal(coincident,(charges[:,None]-charges[None,:])%denominator==0)
    return series


def local_recovery():
    # y includes a missed reception as a genuine outcome; rates use one common ensemble.
    local_even=np.array([.42,0.,.11,0.])
    local_odd=np.array([0.,.31,0.,.16])
    far_channel=np.array([[.55,.1,.12,.15],[.15,.5,.11,.2],[.30,.4,.77,.65]])
    assert np.allclose(far_channel.sum(axis=0),1.)
    results={}
    for name,channel in (("local",np.eye(4)),("far",far_channel)):
        even,odd=channel@local_even,channel@local_odd
        error=float(np.minimum(even,odd).sum())
        contrast=float(np.abs(even-odd).sum())
        sign_scores=[sum(((-1)**((mask>>i)&1))*(even[i]-odd[i]) for i in range(len(even)))
                     for mask in range(2**len(even))]
        assert abs(max(sign_scores)-contrast)<2e-15 and abs(1-2*error-contrast)<2e-15
        results[name]=dict(optimal_error=error,recoverable_contrast=contrast)
    assert results["far"]["recoverable_contrast"]<results["local"]["recoverable_contrast"]
    return results


def inverse_static_strength():
    x,y=.49,2.25
    trials=[]
    for frequencies,masses in (([1.4],[.23]),([.61,1.4,2.8],[.05,.1,.08])):
        t=np.square(frequencies)
        w=np.array(masses)
        rx=float(w@(t/(x+t)))
        ry=float(w@(t/(y+t)))
        strength=(y-x)*rx*ry/(y*ry-x*rx)
        single=(y*ry-x*rx)/(rx-ry)
        weighted=w/((x+t)*(y+t))
        moments=[float(weighted@t**degree) for degree in range(3)]
        variance=moments[0]*moments[2]-moments[1]**2
        total=float(w.sum())
        assert abs(total*(y*ry-x*rx)-(y-x)*rx*ry-(y-x)*x*y*variance)<5e-16
        assert abs(strength*single/(x+single)-rx)<1e-15
        assert abs(strength*single/(y+single)-ry)<1e-15
        if len(t)==1:
            assert abs(strength-total)<2e-14 and abs(single-t[0])<2e-13
        else:
            assert 0<strength<total and variance>0
        trials.append(dict(squared_widths=[x,y],work_per_squared_current=[rx,ry],
                           spectral_mass=total,minimal_mass=strength,equivalent_squared_gap=single))
    return trials


def figure(values):
    fig,axes=plt.subplots(1,2,figsize=(8.2,3.15),layout="constrained")
    t=np.geomspace(.07,14,230)
    for delta,color in ((.65,"#295f87"),(1.5,"#b05a32")):
        early=-np.expm1(-t)
        q=early-np.abs(np.expm1(-(1+1j*delta)*t))/math.hypot(1,delta)
        axes[0].loglog(t,q,label=rf"$\Delta/\kappa={delta}$",color=color)
    axes[0].set(xlabel=r"Exposure since first quantum, $\kappa T$",ylabel="Error-free probability per pair")
    sig,low,upper,both=np.asarray(values["edge"]["edge_scan"]).T
    for y,label,style in ((low,"Bound lines","-"),(upper,"Ionization continuum","--"),(both,"Both parts","-.")):
        axes[1].semilogx(sig,y,style,label=label)
    axes[1].invert_xaxis()
    axes[1].set(xlabel=r"Resolution $\sigma$ (Hartrees)",ylabel="Imaginary part of edge response")
    for ax in axes:
        ax.legend(frameon=False,fontsize=8)
        ax.grid(alpha=.2)
    path=ROOT/"manuscripts"/"autonomous_gravity_cascade.pdf"
    path.parent.mkdir(parents=True,exist_ok=True)
    fig.savefig(path,metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)


if __name__=="__main__":
    result=dict(packets=cascades(),atom=atom(),optical=collective(),edge=threshold_edges(),
                stopped_contact=stopped_mediator(),two_widths=inverse_static_strength(),
                sidebands=recoil_resolved_sidebands(),parity_recovery=local_recovery(),
                compact_momentum=compact_membrane_transfer(),microscopic_work=microscopic_work())
    dest=ROOT/"verification"/"autonomous-gravity-cascade-results.json"
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf-8")
    figure(result)
    print(json.dumps(result,indent=2))
