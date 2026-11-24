"""Surface thermodynamics, causal capture and the Schwarzschild photon spectrum.

Run from the project root with Python 3, NumPy and SciPy. All randomness is
absent. The scattering integration uses c=hbar=G=k_B=1 and r_s=1.
"""
import argparse
import json
from math import acos, log, pi, sqrt, tan
from pathlib import Path

import numpy as np
from scipy.integrate import quad, simpson
from scipy.interpolate import CubicSpline
from scipy.optimize import brentq

OUTPUT = Path(__file__).resolve().parents[1] / "verification" / "fusion-surface-memory-results.json"
LN2 = log(2)
S0 = LN2/2
SOLAR_TIME = 4.92549095e-6
PLANCK_LENGTH = 1.616255e-35
EV_S = 6.582119569e-16


def surface_example():
    z = .5
    radius_rs = 1/(1-z*z)
    rs_time = 6*SOLAR_TIME
    radius_time = radius_rs*rs_time
    sigma = (1-z*z)**2/(4*S0)
    w = z/radius_rs*quad(lambda r: r/(1+sqrt(r)),radius_rs,1.5)[0]
    c2 = .7
    core = (1-z)/(4*pi*sigma)
    tangent = (1+z)/(4*z)
    mode_sq = (1+z)*(.5-(1-3*z*z)/(4*z*z))
    a_time = rs_time*(2/3)*1.5**1.5
    t_h = 1/(4*pi*rs_time)
    x = lambda y: (1+y**1.5)/4
    def adm(y_rad):
        v = x(y_rad**-2)
        return y_rad*(v-v*v/2)
    eps = .0001
    second = (adm(1+eps)+adm(1-eps)-2*adm(1))/eps**2
    assert abs(second/x(1)-mode_sq)<1.5e-6
    assert abs(4*z*(3/8)-(1-z*z))<1e-14
    def onset(required):
        return brentq(lambda re: z/radius_rs*quad(lambda r:r/(1+sqrt(r)),radius_rs,re)[0]-required,
                      radius_rs,100.)
    bound=[]
    for name,kg,metres in (("person",70.,.85),("grain",1.31e-9,5.e-5)):
        # Weakly self-gravitating code estimate in the rest system, not an
        # entropy assigned to a particular actual quantum state.
        c=299792458.
        bits=2*pi*kg*c*metres/(1.054571817e-34*LN2)
        cap_radius=sqrt(4*bits/(pi*sigma))*PLANCK_LENGTH
        frac=2*pi*pi*z*metres/(c*w*radius_time*LN2)
        bound.append(dict(material=name,mass_kg=kg,radius_m=metres,
                          upper_code_bits=bits, storage_patch_radius_m=cap_radius,
                          parallel_pulse_energy_fraction=frac))
    target_error=.01
    binary_cost=(1-2*target_error)*log((1-target_error)/target_error)
    energy_time=2*binary_cost/pi
    one_cell=w*core
    miss=brentq(lambda a:(1-2*a)*log((1-a)/a)-pi*one_cell/2,.000001,.5)
    lone_charge=tan((1-target_error)*pi/2)
    arrival=dict(coherent_symmetric_target_error=target_error, necessary_energy_time=energy_time,
                 necessary_energy_eV=EV_S*energy_time/(w*radius_time), min_one_cell_error=miss,
                 one_flying_charge_energy_time=lone_charge, one_flying_charge_energy_eV=EV_S*lone_charge/(w*radius_time))
    lower_z=brentq(lambda v:15*v**3+3*v*v-v-1.,.33,.5)
    return dict(early_charge=arrival, material_loads=bound, kappa_for_one_gap_time=w*core,
                gap_time_seed_radius_rs=onset(1/core), swap_seed_radius_rs=onset(pi/core),
                locked_sound_min_lapse=lower_z, min_radius_rs=1/(1-lower_z**2),
                z=z, radius_rs=radius_rs, radius_m=radius_time*299792458,
                a_fall_us=a_time*1e6, b_lead_us=w*radius_time*1e6, local_window=w,
                sound_speed_sq=c2, sound_reach_m=sqrt(c2)*w*radius_time*299792458,
                radial_omega_sq_R_sq=mode_sq, radial_center_difference=second/x(1),
                phase_active_empty_adm_fraction=(.25-.25**2/2)/adm(1),
                cell_density_planck=sigma, spacing_planck=1/sqrt(sigma),
                proper_energy_per_defect_R=core, min_swap_gap_R=pi/w,
                min_swap_gap_eV=pi*EV_S/(w*radius_time), gap_over_cell_energy=pi/(w*core),
                log_slope=tangent, T_H_eV=t_h*EV_S,
                excitation_cost_two_cells_over_TH=LN2,
                radial_phase_advance=sqrt(mode_sq)*w,
                speed_limit_duration_in_units_R=pi/(2*core))


def intrinsic_boundaries():
    # One-sided Schwarzschild, R*=1, r_s=3/4. The two square-root
    # actions agree on every static sphere but have different time derivatives.
    def pressure_difference(u,amp,jets):
        r=1+amp*jets[0]
        v,acc,jerk,snap=amp*np.asarray(jets[1:])
        y=r**-2
        mass=u-1+(1+y**1.5)/4
        pressure_material=.75*y**1.5-mass
        f=1-.75/r
        lapse=sqrt(f+v*v)
        pressure_exterior=lapse+(r*acc+.375/r)/lapse
        radicand=u*u+v*v+2*r*acc
        length=sqrt(radicand)
        first=(4*v*acc+2*r*jerk)/(2*length)
        second=(4*acc**2+6*v*jerk+2*r*snap)/(2*length)-first**2/length
        chi_d=v/(2*length)-r*first/(2*length**2)
        chi_dd=acc/(2*length)-v*first/length**2-r*second/(2*length**2)+r*first**2/length**3
        pressure_geometry=length+r*acc/length+2*r*(chi_dd+v*chi_d/r)
        return pressure_exterior-pressure_geometry-pressure_material
    rows=[]
    for u in (sqrt(2),2.):
        stiffness=.375
        c=2-3/u
        roots=np.roots([1/u**3,-c,stiffness])
        errors=[]
        for jets in ([.7,.4,-.6,.8,.3],[-.1,.6,.8,-.1,.5],[1.,0,0,0,0],[0,0,0,0,1.]):
            eps=2.e-5
            finite=(pressure_difference(u,eps,jets)-pressure_difference(u,-eps,jets))/(2*eps)
            linear=jets[4]/u**3+c*jets[2]+stiffness*jets[0]
            errors.append(abs(finite-linear))
        assert max(errors)<2e-8
        rows.append(dict(u=u, scalar_pressure_over_energy=(1.25-u)/(2*(u-.5)),
                         density_derivative_ratio=(11/16-1/(2*u)+1/(4*u**3))/(1/8+1/(2*u)),
                         full_curvature_discriminant=c*c-1.5/u**3,
                         full_curvature_poles=[[float(a.real),float(a.imag)] for a in roots],
                         exact_pressure_linearization_error=max(errors), slice_omega_sq=3/16))
    xh=7/16
    # R=R0 cos^2(theta) removes the integrable endpoint at zero initial speed.
    theta=acos(sqrt(xh))
    exact=(theta+sqrt(xh*(1-xh)))/sqrt(xh)
    numeric=quad(lambda t:2*np.cos(t)**2/sqrt(xh),0,theta)[0]
    assert abs(exact-numeric)<1.e-13
    return dict(examples=rows, empty_horizon_radius_ratio=xh, empty_infall_speed_at_horizon=.75,
                empty_time_to_trap_over_R0=exact,
                illustrative_empty_time_us=exact*(4/3)*6*SOLAR_TIME*1.e6)


def exchange_gate():
    # Jordan-Wigner representation of four Majoranas on two complex modes.
    identity = np.eye(2,dtype=complex)
    x = np.array([[0,1],[1,0]],complex)
    y = np.array([[0,-1j],[1j,0]])
    z = np.diag([1,-1])
    gamma = [np.kron(x,identity),np.kron(y,identity),np.kron(z,x),np.kron(z,y)]
    keep = [0,3]
    def even(a,b):
        return (1j*gamma[a]@gamma[b])[np.ix_(keep,keep)]
    zz,xx = even(0,1),even(1,2)
    yy = -1j*zz@xx
    assert np.max(abs(xx@zz+zz@xx))<1e-13
    assert np.max(abs(yy@yy-identity))<1e-13
    swap = (np.eye(4)+np.kron(xx,xx)+np.kron(yy,yy)+np.kron(zz,zz))/2
    target = np.eye(4)[[0,2,1,3]]
    assert np.max(abs(swap-target))<1e-14
    # Midpoint boundary prescription for one right-moving carrier and impurity.
    def phase(strength):
        return (1-1j*strength/2)/(1+1j*strength/2)
    strength=8/sqrt(3)
    factors = []
    for ratio in (.5,.9,1,1.1,2):
        triplet = phase(ratio*strength/4)
        singlet = phase(-3*ratio*strength/4)
        # Unknown input on a two-level rail, blank receiver. After tracing the
        # rail the excitation transfer is amplitude damping up to a known phase.
        transferred = abs((triplet-singlet)/2)
        factors.append(dict(strength_over_matched=ratio, transfer=transferred**2,
                            entanglement_fidelity_after_phase=(1+transferred)**2/4))
    assert abs(factors[2]["transfer"]-1)<1e-14
    return dict(swap_error=float(np.max(abs(swap-target))), coupling_over_v=strength,
                detuned=factors)


def start_at_horizon(k, ell, offset, spin):
    # Unit ingoing amplitude times the near-horizon Frobenius series.
    ll=ell*(ell+1)
    past=np.zeros_like(k,dtype=complex)
    coeff=np.ones_like(k,dtype=complex)
    amp=coeff.copy()
    deriv=np.zeros_like(amp)
    screened=coeff.copy()
    for n in range(12):
        nxt=((ll-n*(n-1)+4j*k*n)*coeff+2j*k*(n-1)*past+(1-spin**2)*screened)/((n+1)*(n+1-2j*k))
        amp+=nxt*offset**(n+1)
        deriv+=(n+1)*nxt*offset**n
        past,coeff=coeff,nxt
        screened=nxt-screened
    f=offset/(1+offset)
    return amp, f*deriv-1j*k*amp


def start_at_infinity(k, ell, far, order, spin):
    # Outgoing phase times its r^{-1} expansion. Absolute phases cancel.
    ll=ell*(ell+1)
    arg=k*far
    past=np.zeros_like(k,dtype=complex)
    coeff=np.ones_like(k,dtype=complex)
    amp=coeff.copy()
    deriv=np.zeros_like(amp)
    for n in range(order):
        nxt=((n*(n+1)-ll)*coeff-k*((n-1)*(n+1)+1-spin**2)*past)/(2j*(n+1))
        amp+=nxt/arg**(n+1)
        deriv-=(n+1)*nxt/arg**(n+1)/far
        past,coeff=coeff,nxt
    f=1-1/far
    return amp, f*deriv+1j*k*amp


def propagate(state,k,ell,left,right,steps,spin):
    """Fourth-order evolution on a uniform grid in log(r-1), vectorized in k."""
    y,v=state
    step=(right-left)/steps
    advance=np.exp(step)
    half_advance=np.sqrt(advance)
    offset=np.exp(left)
    ll=ell*(ell+1)
    def slopes(u,amplitude,gradient):
        r=1+u
        return r*gradient,((ll+(1-spin*spin)/r)*u/r**2-k*k*r)*amplitude
    for _ in range(steps):
        mid=offset*half_advance
        end=offset*advance
        a,b=slopes(offset,y,v)
        c,d=slopes(mid,y+step*a/2,v+step*b/2)
        e,f=slopes(mid,y+step*c/2,v+step*d/2)
        g,h=slopes(end,y+step*e,v+step*f)
        y=y+step*(a+2*c+2*e+g)/6
        v=v+step*(b+2*d+2*f+h)/6
        offset=end
    return y,v


def greybody(k,ell,scale,spin):
    # The conserved Wronskian of the two solutions gives transmission from
    # infinity or from the horizon. Use wave numbers in Schwarzschild units.
    off=.025
    far=np.maximum(13., (21+ell)/k)
    match=np.log(2.)
    a,b=propagate(start_at_horizon(k,ell,off,spin),k,ell,np.log(off),match,120*scale,spin)
    c,d=propagate(start_at_infinity(k,ell,far,18,spin),k,ell,np.log(far-1),match,260*scale,spin)
    trans=4*k*k/abs(a*d-b*c)**2
    return trans


def radiation_spectrum(step, ellmax=8, scale=1, xmax=36, spin=1):
    x=np.arange(0,xmax+step/2,step)
    k=x[1:]/(4*pi)
    density=np.zeros_like(x)
    per_ell=[]
    for ell in range(spin,ellmax+1):
        # Richardson removes the leading RK4 phase and normalization errors.
        one=greybody(k,ell,scale,spin)
        two=greybody(k,ell,2*scale,spin)
        prob=two+(two-one)/15
        if prob.min()<=0 or prob.max()>1.00003:
            raise ValueError((ell,prob.min(),prob.max()))
        partial=2*(2*ell+1)*prob/np.expm1(x[1:])
        term=np.concatenate(([0.],partial))
        density+=term
        per_ell.append(float(simpson(x*term,x=x)/(128*pi**3)))
    return statistics(x,density,per_ell),x,density


def statistics(x,density,per_ell):
    total=simpson(density,x=x)
    # Total energy per Schwarzschild time gives -M^2 dM/dt for two polarizations.
    power=simpson(x*density,x=x)/(128*pi**3)
    tail_occupation=simpson(x*x*density,x=x)/total
    moments=[]
    for gap in (LN2,2*LN2,4*LN2):
        for harmonic in (1,2):
            phase=2*pi*harmonic/gap
            moment=simpson(density*np.sin(phase*x),x=x)/total
            moments.append(dict(gap_over_TH=gap,harmonic=harmonic, sine=float(moment),
                                min_mean_pair_detuning_over_TH=float(2*abs(moment)/phase)))
    return dict(power=float(power),mean_x=float(simpson(x*density,x=x)/total),
                mean_x_sq=float(tail_occupation),partial_powers=per_ell,moments=moments)


def folded_construction(x,density,gap):
    # The conditional bin law restores the entire real-frequency marginal.
    spline=CubicSpline(x,density)
    ngrid=512
    residue=np.arange(ngrid)/ngrid
    grid=gap*(residue[:,None]+np.arange(int(x[-1]/gap)+1)[None,:])
    vals=np.where(grid<=x[-1],np.maximum(0,spline(grid)),0.)
    folded=gap*vals.sum(axis=1)/simpson(density,x=x)
    folded/=folded.mean()
    rev=folded[(-np.arange(ngrid))%ngrid]
    even=(folded+rev)/2
    odd=(folded-rev)/2
    if min(even)<=2/3:
        raise ValueError("This interpolation needs a different positive triple coupling")
    # Include a small numerical margin when constructing the mixed distribution.
    triple_fraction=1.001*max(abs(odd)/(even-2/3))
    channel=even+odd/triple_fraction
    idx=np.arange(ngrid)
    third=(-idx[:,None]-idx[None,:])%ngrid
    joint=channel[:,None]+channel[None,:]+channel[third]-2
    recovered=((1-triple_fraction)*even+triple_fraction*joint.mean(axis=1))
    assert joint.min()>-1e-10 and max(abs(recovered-folded))<3e-14
    # Independent evaluation of the first sine moment directly on the residues.
    moment=float(np.mean(folded*np.sin(2*pi*residue)))
    return dict(gap_over_TH=gap, minimum_density=float(min(folded)),
                maximum_density=float(max(folded)), residual_sine=moment,
                unavoidable_unpaired_fraction=float(np.mean(abs(odd))),
                sufficient_triple_fraction=float(triple_fraction),
                triple_density_minimum=float(joint.min()),
                three_marginal_error=float(max(abs(recovered-folded))))


def recoil_check():
    # Future-directed null vectors. Solve the two-body invariant-mass equation
    # exactly for an arbitrary direction-space distribution inside one cluster.
    out=[]
    for mass,energies,directions in [
            (100.,[.2,.3,.7],[[1,0,0],[0,1,0],[0,0,1]]),
            (10.,[.3,1.2,1.5],[[0,1,0],[0,1,0],[0,-1,0]]),
            (2.,[.1,.2,.3],[[1,0,0],[1,0,0],[1,0,0]])]:
        total=sum(energies)
        momentum=np.asarray(energies)@np.asarray(directions)
        ksq=total*total-float(momentum@momentum)
        scale=2/(1+sqrt(1-2*ksq/(mass*total)))
        final_invariant=(mass-scale*total)**2-scale**2*float(momentum@momentum)
        err=abs(final_invariant-(mass**2-2*mass*total))
        assert err<5e-11
        out.append(dict(scale=scale, mass_shell_error=err))
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure", help="Write the article figure to this PDF.")
    args=parser.parse_args()
    surf=surface_example()
    gate=exchange_gate()
    # Coarse and fine grids run the full spectrum independently.
    refs={}
    checks={}
    for spin in (1,2):
        coarse,xc,dc=radiation_spectrum(1/16,ellmax=7,scale=4,spin=spin)
        fine,x,df=radiation_spectrum(1/32,ellmax=8,scale=4,spin=spin,xmax=42)
        refs[spin]=(fine,df)
        checks[spin]=(coarse,dc)
        for first,second in zip(coarse["moments"],fine["moments"]):
            second["grid_difference"]=abs(first["sine"]-second["sine"])
    photons,density=refs[1]
    gravitons,graviton_density=refs[2]
    total_density=density+graviton_density
    combined=statistics(x,total_density,[])
    coarse_both=statistics(xc,checks[1][1]+checks[2][1],[])
    for first,second in zip(coarse_both["moments"],combined["moments"]):
        second["grid_difference"]=abs(first["sine"]-second["sine"])
    # Compare against the preceding radial refinement to check the small oscillatory moment independently.
    dense_radial=[]
    for spin in (1,2):
        _,_,density_refined=radiation_spectrum(1/32,ellmax=8,scale=2,xmax=42,spin=spin)
        dense_radial.append(density_refined)
    deep=statistics(x,dense_radial[0]+dense_radial[1],[])
    for current,refined in zip(combined["moments"],deep["moments"]):
        current["radial_difference"]=abs(current["sine"]-refined["sine"])
        assert current["radial_difference"]<2.e-9
        current["recoil_mass_threshold_planck"]=sqrt(
            current["harmonic"]*combined["mean_x_sq"]/(4*current["gap_over_TH"]*abs(current["sine"])))
    folds=[folded_construction(x,total_density,a*LN2) for a in (1,2,4)]
    for row,direct in zip(folds,combined["moments"][::2]):
        assert abs(row["residual_sine"]-direct["sine"])<5e-8
    assert abs(photons["power"]-3.3638e-5)<1e-9
    assert abs(gravitons["power"]-3.836e-6)<1e-9
    result=dict(surface=surf,one_sided=intrinsic_boundaries(),impurity=gate,black_hole_photons=photons,
                black_hole_gravitons=gravitons,combined=combined,folded=folds,
                finite_recoil=recoil_check())
    OUTPUT.write_bytes((json.dumps(result,indent=2,sort_keys=True,allow_nan=False)+"\n").encode())
    if args.figure:
        from matplotlib import pyplot as plt
        plt.rcParams.update({"font.size":9,"axes.spines.top":False,"axes.spines.right":False,
                             "pdf.fonttype":42})
        fig,(left,right)=plt.subplots(1,2,figsize=(7.0,2.85),layout="constrained")
        zz=np.linspace(.30,.63,240)
        lower=(1-3*zz*zz)/(4*zz*zz)
        upper=3*zz/(1+zz)
        left.fill_between(zz,lower,upper,where=lower<upper,color="#cbdcce")
        left.plot(zz,lower,color="#244e63",label="Radial stability floor")
        left.plot(zz,upper,color="#934d2d",label="Material sound ceiling")
        left.scatter([.5],[.5],color="black",s=22,zorder=4,label="Two-current surface")
        left.set(xlabel="Surface lapse z",ylabel="Density response nF'' / F'",ylim=(-.22,1.75),
                 title="Uniform spherical equilibrium")
        left.legend(fontsize=7,frameon=False)
        gap=2*LN2
        phase=np.linspace(0,1,513)
        law=CubicSpline(x,total_density)
        def folded(t):
            grid=gap*(t[:,None]+np.arange(int(x[-1]/gap)+1)[None,:])
            return gap*np.where(grid<=x[-1],np.maximum(0,law(grid)),0.).sum(axis=1)/simpson(total_density,x=x)
        skew=(folded(phase)-folded(1-phase))*500000.
        right.axhline(0,linewidth=.8,color="#a6572d",label="Sharp two-particle energy sum")
        right.plot(phase,skew,color="#254e65",label="Hawking photons and gravitons")
        right.set(xlabel="Energy modulo the four-vortex step (cycles)",ylabel="Odd part of density (ppm)",
                  xlim=(0,1),title="Reflection of the emitted spectrum")
        right.legend(loc="upper right",frameon=True,framealpha=.95,edgecolor="none",fontsize=6.5)
        fig.savefig(args.figure,metadata={"CreationDate":None,"ModDate":None});plt.close(fig)
    print(OUTPUT.name)


if __name__=="__main__":
    main()
