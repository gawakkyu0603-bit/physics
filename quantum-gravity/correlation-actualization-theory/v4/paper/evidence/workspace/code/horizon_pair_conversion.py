"""Boundary mass conversion, correlated pair radiation, and a moving resonator.

Units use hbar=c=1.  No random samples.  Pass an output path to reproduce the JSON.
"""
import argparse
import itertools
import json
from functools import lru_cache
from math import ceil, exp, log, pi, sin, sqrt, tanh
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import expm
from scipy.optimize import brentq


def integrate(rhs, span, initial, **kwargs):
    solution = solve_ivp(rhs, span, initial, method="DOP853", rtol=2e-11, atol=3e-13, **kwargs)
    if not solution.success:
        raise RuntimeError(solution.message)
    return solution


def log_weight(k, mass, duration):
    initial = np.hypot(k, mass)
    # Subtract logarithms after factoring the leading exponential from each sinh.
    small = pi*duration*mass**2/(initial+k)
    large = pi*duration*(initial+k)
    return -2*pi*duration*k + 2*(np.log(-np.expm1(-small))-np.log(-np.expm1(-large)))


def quench():
    rows = []
    for mass, duration, k in [(2, .35, .25), (5, .8, .7), (9, .6, 1.2), (2, .5, 2)]:
        wi = np.hypot(k, mass)
        start = 16*duration
        def rhs(t, state):
            return [state[1], -(k*k+mass*mass*(1-tanh(t/duration))/2)*state[0]]
        sol = integrate(rhs, (-start, start), [1/sqrt(2*wi)+0j, -1j*sqrt(wi/2)])
        q, p = sol.y[:, -1]
        a = (k*q+1j*p)/sqrt(2*k)
        b = (k*q-1j*p)/sqrt(2*k)
        measured = abs(b/a)**2
        exact = exp(log_weight(k, mass, duration))
        assert abs(measured/exact-1)<4e-8 and abs(abs(a)**2-abs(b)**2-1)<3e-9
        rows.append(dict(mass=mass,proper_time=duration,omega=k,numerical=measured,
                         exact=exact,deep=exp(-2*pi*duration*k),wronskian=abs(a)**2-abs(b)**2))
    modes=np.arange(1,10001)*.002
    weights=np.exp(log_weight(modes,9,1))
    finite=float(np.sum(2*2*modes*weights/(1-weights)))
    continuum=2*pi*(2*pi/.002)/(6*(2*pi)**2)
    return dict(scattering=rows,energy_two_flavours=finite,continuum=continuum,
                proper_hawking_time_us=4*3*4.925490947/3,
                local_acceleration_to_hawking_timescale=(9/8)**2)


def conservative_clock():
    # A finite set of real standing oscillators. The potential subtracts their
    # instantaneous ground energy. Include the derivative of the same subtraction.
    k=np.array([.55,.9,1.5,2.1]); mass=4.; inertia=100.
    rows=[]
    for surplus in [0.,.08,1.]:
        angle=.025
        wi=np.sqrt(k*k+mass**2*(1+np.cos(angle))/2)
        speed=sqrt(sin(angle)**2+2*surplus/inertia)
        initial=np.r_[angle,speed,1/np.sqrt(2*wi)+0j,-1j*np.sqrt(wi/2)]
        def rhs(t,state):
            angle,speed=state[:2].real
            q,p=np.split(state[2:],2)
            freq=np.sqrt(k*k+mass**2*(1+np.cos(angle))/2)
            dm2=-mass**2*np.sin(angle)/2
            force=inertia*np.sin(angle)*np.cos(angle)-.5*dm2*np.sum(abs(q)**2-1/(2*freq))
            return np.r_[speed,force/inertia,p,-freq**2*q]
        def stop(t,state): return state[0].real-pi
        stop.terminal=True;stop.direction=1
        sol=integrate(rhs,(0,12),initial,events=stop,max_step=.05)
        angles,speeds=sol.y[:2].real
        q,p=np.split(sol.y[2:],2)
        w=np.sqrt(k[:,None]**2+mass**2*(1+np.cos(angles))/2)
        excit=np.sum((abs(p)**2+w*w*abs(q)**2-w)/2,axis=0)
        total=inertia*(speeds**2+np.cos(angles)**2)/2+excit
        drift=float(np.ptp(total))
        assert drift<1e-8
        crossed=bool(len(sol.t_events[0]))
        if not surplus: assert not crossed
        rows.append(dict(initial_surplus=surplus,crossed=crossed,last_time=float(sol.t[-1]),
                         maximum_angle=float(np.max(angles)),last_excitation=float(excit[-1]),
                         energy_drift=drift))
    return rows


def fronts():
    rows=[]
    for h in [.25,.5,.8]:
        rows.append(dict(h=h,beta_plus_over_geometric=1/(1+h),
                         beta_minus_over_geometric=1/(1-h),pair_temperature_inverse_ratio=1/(1-h*h),
                         partner_momentum_ratio=(1+h)/(1-h),energy_with_no_tangential_sink=(1-h)**2/(1+h*h)))
    return rows


@lru_cache(None)
def comps(n,d):
    if d==1: return [(n,)]
    return [(a,)+tail for a in range(n+1) for tail in comps(n-a,d-1)]


def port(n,C):
    d=len(C); source=comps(n,d); output=comps(n-1,d)
    idx={p:i for i,p in enumerate(output)}
    B=np.zeros((len(output)**2,len(source)**2),complex)
    for col,(l,r) in enumerate(itertools.product(source,repeat=2)):
        for a,b in itertools.product(range(d),repeat=2):
            if l[a] and r[b]:
                ll=list(l); rr=list(r); ll[a]-=1; rr[b]-=1
                B[len(output)*idx[tuple(ll)]+idx[tuple(rr)],col]+=C[a,b]*sqrt(l[a]*r[b])
    return B


def scalar(n,d):
    m=len(comps(n,d))
    return np.eye(m).ravel()/sqrt(m)


def coherences():
    d=2
    basis=[np.diag([1,-1])/sqrt(2),np.array([[0,1],[0,0]]),np.array([[0,0],[1,0]])]
    C=np.array([[1+.4j,.2j],[.3+.1j,-.7+.2j]])
    W=np.linalg.norm(C)**2; S=abs(np.trace(C))**2
    rows=[]
    for n in range(1,9):
        B=[port(n,c) for c in basis]
        K=sum(b.conj().T@b for b in B)
        eig=np.linalg.eigvalsh(K)
        pair=scalar(n,d)
        E=float(np.linalg.norm(port(n,C)@pair)**2)
        D=float(np.linalg.norm(port(n+1,C).conj().T@pair)**2)
        m=n/d; A=n*(n-1)/(d*(d+1))
        assert abs(E-(A*W+(A+m)*S))<2e-11
        assert abs(D-((A+2*m+1)*W+(A+m)*S))<2e-11
        assert abs(eig[0]-n*(n-1)/2)<1e-10
        rows.append(dict(n=n,minimum_rate=float(eig[0]),dark_dimension=int(sum(eig<1e-11)),
                         emission=E,reverse=D))
    return rows


def moving_port():
    # No-jump propagator and free reference in the interaction picture.
    # The port is a unit vector in a real two-dimensional subspace of pair states.
    def rhs(t,y):
        theta=.6*t+.3*sin(1.4*t)
        w=np.array([np.sin(theta),np.cos(theta)])
        width=.7+.2*np.cos(t)
        return np.r_[-width*w*np.dot(w,y[:2])/2,width*w[0]**2]
    sol=integrate(rhs,(0,12),[1.,0.,0.])
    state=sol.y[:2,-1]; I=float(sol.y[-1,-1]);P=float(state@state)
    bound=4*(1-sqrt(P))/(1+sqrt(P))
    assert I>=bound
    return dict(duration=12.,survival=P,free_exposure=I,necessary_exposure=bound,
                q_at_one_percent=2/299,minimum_average_exposure_at_99_percent=36*299/22)


def final_resonance():
    def survival(x):
        return exp(-x/2)*((1+x/4)**2+(x/4)**2)
    needed=brentq(lambda x:survival(x)-.01,10,24)
    G=np.array([[0,-.25j],[-.25j,-.5]])
    assert abs(np.linalg.norm(expm(needed*G)[:,0])**2-.01)<1e-12
    # Exterior eq. (zs-regular). Radii and retarded time in L.
    s=1/sqrt(24); B=5*s
    def geometry(r,offset):
        charge=2*s*r**3/(1+r**3)
        za=B-s-charge; compact=2*B*charge-charge**2
        delta_z2=compact*offset/(r+offset)
        zb=sqrt(za**2+delta_z2)
        return za,delta_z2/(za+zb),charge
    rows=[]
    for scale,offset,chosen_omega,line_fraction in [
        (1e6,.02,1000.,.001),(1e6,.02,30000.,.001),
        (1e6,.02,None,.001),(1e6,.1,None,.015),
        (1e12,.0005,None,.000025),(1e12,.0005,None,.000075),
        (1e15,.0001,None,.00001),(1e17,.0001,None,.00001)]:
        cut=brentq(lambda r:scale**2*r*r*geometry(r,.01)[2]-1,1e-12,.1,xtol=1e-16)
        omega=1/cut if chosen_omega is None else chosen_omega
        def rhs(r,y):
            za,dz,_=geometry(r,offset)
            du=-1/(s*za)
            kap=line_fraction*omega*za
            g=kap/4; delta=omega*dz
            a,b=y[:2]
            return du*np.array([-1j*g*b, -1j*g*a-(.5*kap+1j*delta)*b,
                                 kap*abs(b)**2,1,kap],complex)
        y=integrate(rhs,(1,cut),[1+0j,0j,0j,0j,0j],max_step=.005).y[:,-1]
        prob=float(abs(y[0])**2+abs(y[1])**2)
        za,dz,_=geometry(1,offset);zaf,dzf,_=geometry(cut,offset)
        initial_det=dz/(za*line_fraction)
        gamma_fraction=(1/16)/(initial_det**2+.25)
        ratio=2*gamma_fraction/(3+gamma_fraction)
        weak_probe_ratio=(.25+.5*ratio)/(1+.5*ratio)
        assert abs(prob+y[2].real-1)<1e-8
        ri=brentq(lambda r:scale**2*r*r*geometry(r,.01)[2]-2,cut,1,xtol=1e-16)
        late=integrate(rhs,(ri,cut),[1+0j,0j,0j,0j,0j]).y[:,-1]
        exposure=line_fraction*omega*(ri-cut)/s
        # Integrate the tiny radiated probability divided by X^3, with an
        # order-one amplitude b/X, so the absolute error scale is meaningful.
        def scaled(frac,state):
            za,dz,_=geometry(ri-(ri-cut)*frac,offset)
            detuning=dz/(line_fraction*za)
            a,b,emission=state
            return [-1j*exposure**2*b/4,-1j*a/4-exposure*(.5+1j*detuning)*b,abs(b)**2]
        scaled_emission=float(integrate(scaled,(0,1),[1+0j,0j,0j]).y[2,-1].real)*exposure**3
        assert abs(scaled_emission-late[2].real)<1e-6*scaled_emission
        rows.append(dict(last_two_radius_ratio=ri/cut,last_two_exposure=float(late[4].real),
                         last_two_radiated=scaled_emission,unscaled_check=float(late[2].real),
                         full_loop_ports_for_coverage=ceil(4*pi*s/log(ri/cut)),
                         scale_in_planck_lengths=scale,cutoff_radius=cut,terminal_line_to_energy=omega*cut,
                         maximum_linewidth_times_delay=2*offset*line_fraction*omega*zaf/(za*za),
                         resonant_minimum_survival=survival(y[4].real),
                         offset=offset,proper_frequency=omega,fractional_linewidth=line_fraction,
                         initial_detuning_linewidths=initial_det,final_detuning_linewidths=dzf/(zaf*line_fraction),
                         initial_dispersive_spectral_excess=weak_probe_ratio/.25-1,
                         integrated_width=float(y[4].real),survival=prob,radiated=float(y[2].real),
                         retarded_time=float(y[3].real),max_signal_delay=2*offset/(za*za),
                         largest_travel_phase=2*offset*omega/(za*za)))
        assert prob+1e-8>=survival(y[4].real)
    return dict(critical_time_in_linewidths=needed,branches=rows)


def fall_window():
    rs_time=2*3*4.925490947  # microseconds
    c=299.792458  # metres per microsecond
    cases=[]
    for x in [1.01,9/8,1.3]:
        z=sqrt(1-1/x)
        advanced=rs_time*quad(lambda t:t/(1+sqrt(t)),x,1.5)[0]
        budget=z*advanced
        ramp=log(9)*2*rs_time*z
        closed_storage=(ramp-budget)*c/2
        cases.append(dict(boundary_radius_in_rs=x,advanced_us=advanced,tube_proper_us=budget,
                          central_ramp_us=ramp,minimum_extra_us=ramp-budget,
                          light_speed_storage_one_way_metres=closed_storage))
    return cases


def electromagnetic_pulse():
    # A round world tube contracts at constant flat-frame speed V.  Three
    # orientations may be summed to distribute the dipole stress isotropically.
    V=.2; alpha=V/(1+V); boost=(1+V)/(1-V)
    c2=alpha**4
    c1=2.5*c2-(1-alpha)*alpha**2
    c0=9*c2/16-2.25*(1-alpha)*alpha**2-(1-alpha)*(1-4*alpha)/2
    a=c2*512/35; b=c1*16/7
    spectral_root=(-b+sqrt(b*b-4*a*c0))/(2*a)
    balanced_span=pi/sqrt(spectral_root)

    discriminant=sqrt(c1*c1-4*c2*c0)
    osc=sqrt((-c1+discriminant)/(2*c2))
    hyp=sqrt((c1+discriminant)/(2*c2))
    endpoint=lambda Y:osc*np.tan(osc*Y/2)+hyp*np.tanh(hyp*Y/2)
    stationary_span=brentq(endpoint,pi/osc+1e-8,2*pi/osc-1e-8)

    def pulse(span,stationary=False):
        ratio=exp(span)
        def shape(y):
            if stationary:
                z=y-span/2
                weight=np.cos(osc*span/2)/np.cosh(hyp*span/2)
                return (np.cos(osc*z)-weight*np.cosh(hyp*z),
                        -osc*np.sin(osc*z)-weight*hyp*np.sinh(hyp*z),
                        -osc**2*np.cos(osc*z)-weight*hyp**2*np.cosh(hyp*z))
            arg=pi*y/span
            return (np.sin(arg)**4,(pi/span)*(np.sin(2*arg)-.5*np.sin(4*arg)),
                    (pi/span)**2*(2*np.cos(2*arg)-2*np.cos(4*arg)))
        def at(y):
            R=ratio*np.exp(-y)
            f,f1,f2=shape(y)
            p=R**1.5*f
            dp=alpha*R**.5*(f1-1.5*f)
            ddp=alpha**2*R**(-.5)*(f2-2*f1+.75*f)
            H=dp/R;J=p/R**2
            D=ddp+H+J; C=ddp+H
            e=.5*(D*D+C*C)+ (H+J)**2
            flux=D*C; pressure=.5*(D*D+C*C)-(H+J)**2
            measure=R/alpha
            local_pressure=(pressure+2*V*flux+V*V*e)/(1-V*V)
            local_power=((1+V*V)*flux+V*(pressure+e))/(1-V*V)
            return ddp**2*measure,local_pressure*measure/sqrt(boost),local_power*measure/sqrt(boost),((1-alpha)*flux+alpha*e)*measure,(dp**2+p*dp/R+.5*p*p/R**2)/R
        def rhs(y,totals):
            return at(y)[:4]
        mesh=np.linspace(0,span,301)
        sol=integrate(rhs,(0,span),[0.,0.,0.,0.],t_eval=mesh,dense_output=True)
        far,impulse,local,sent=sol.y[:,-1]
        reactive=np.asarray([at(y)[4] for y in mesh])
        assert np.max(abs(sol.y[3]-sol.y[0]-reactive))<1e-7*far
        # Locate all extrema of the transferred energy, including endpoints.
        slopes=[at(y)[3] for y in mesh]
        extrema=[0.,span]+[brentq(lambda y:at(y)[3],l,r) for l,r,p,q in
                          zip(mesh[:-1],mesh[1:],slopes[:-1],slopes[1:]) if p*q<0]
        peak=max(float(sol.sol(y)[3]) for y in extrema)
        # Independent use of the logarithmic-coordinate quadratic form.
        base=(35/128)*span
        wave=pi/span
        analytic=sqrt(boost)/alpha*base*(a*wave**4+b*wave**2+c0)
        if stationary:
            assert max(abs(shape(y)[j]) for y in [0,span] for j in [0,1])<1e-9
            def integrated_form(y):
                f,f1,f2=shape(y)
                return c2*f2*f2+c1*f1*f1+c0*f*f
            analytic=sqrt(boost)/alpha*quad(integrated_form,0,span,epsabs=1e-14)[0]
        assert abs(analytic-impulse)<2e-8*far and abs(sent/far-1)<1e-8
        return dict(log_radius_span=span,start_to_end_radius=ratio,charge_ratio_deep=ratio**5,
                    impulse_over_infinity_energy=impulse/far,comoving_energy_over_infinity=local/far,
                    peak_sent_over_final=peak/far,max_reactive_over_final=float(np.max(reactive)/far))
    short=log(2)/5; U=np.expm1(short)/alpha
    rows=[pulse(s) for s in [short,balanced_span*.95,balanced_span,balanced_span*1.05]]
    return dict(bulk_speed=V,alpha=alpha,balanced_span=balanced_span,cases=rows,
                forbidden_span_below=pi/osc,minimum_charge_ratio_from_dirichlet=exp(5*pi/osc),
                stationary_pulse=pulse(stationary_span,True),
                two_charge_time_over_final_radius=U,
                two_charge_impulse_lower_over_boosted_energy=1-(1-alpha)*(U/pi)**2-(1-alpha)*(1-4*alpha)/2*(U/pi)**4)


def release_paths():
    # Incoming exterior is vacuum. Compare port probabilities using amplitudes on
    # the two arms and the overlap of the unobserved gravitational records.
    results=[]
    for eta,dt,overlap in [(.5,0,1),(.5,.04,1),(.49,0,1),(.5,0,.9),(.5,0,0)]:
        w=2.; odd_phase=-np.exp(1j*w*dt)
        arm1=np.array([1,0],complex);arm2=np.array([overlap,sqrt(1-overlap**2)],complex)
        remaining=np.linalg.norm(eta*arm1+(1-eta)*odd_phase*arm2)**2
        outgoing=np.linalg.norm(sqrt(eta*(1-eta))*(arm1-odd_phase*arm2))**2
        assert abs(remaining+outgoing-1)<1e-12
        results.append(dict(mixing=eta,differential_time=dt,omega=w,record_overlap=overlap,
                            remaining=float(remaining),outgoing=float(outgoing)))
    return results


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output",nargs="?",type=Path,default=Path(__file__).resolve().parents[1]/"verification"/"horizon-pair-conversion-results.json")
    outfile=parser.parse_args().output
    report=dict(mass_scattering=quench(),clock=conservative_clock(),fronts=fronts(),pair_ports=coherences(),
                moving_port=moving_port(),resonance=final_resonance(),fall_window=fall_window(),coherent_release=release_paths(),electromagnetic_pulse=electromagnetic_pulse())
    outfile.write_text(json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf8")
    print(outfile.name)
