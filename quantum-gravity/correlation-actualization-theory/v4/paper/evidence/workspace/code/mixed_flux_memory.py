"""Retarded gravitational receipts, counterflow recoil and a single scalar radiation port."""
import argparse
import json
from math import exp, log, pi, sin, sqrt
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.optimize import brentq
from scipy.special import expm1, wrightomega

ROOT = Path(__file__).resolve().parents[1]


def smooth_on(x):
    t = np.clip(x, 0., 1.)
    return t**3 * (10 + t * (-15 + 6*t))


def receipts():
    # Conformal distances in units of the star's comoving radius.  r_s=c=1.
    compactness = 1 / sqrt(2)
    deadline = -2 / sqrt(compactness)
    fully_on = -2 * sqrt(6)
    length_scale = .25

    def source(t):
        return 6 * smooth_on((t - (fully_on - .25))/.25) / t**2

    cuts = []
    for shell, point in [(1., .5), (1., .95), (.5, .45), (.5, 1.)]:
        arrival = fully_on + shell + point
        available_time = length_scale * ((-arrival)**3 - (-deadline)**3) / 3
        scale = length_scale * deadline**2
        distance = shell - deadline
        def response(radius):
            value = quad(lambda t: shell*source(t), deadline-shell-radius,
                         deadline-abs(shell-radius), epsabs=1e-14)[0]
            return value/(2*scale*radius)
        if point<shell:
            exact = 6*shell/(scale*(distance**2-point**2))
            gradient = 12*shell*point/(scale**2*(distance**2-point**2)**2)
        else:
            block=(point-deadline)**2-shell**2
            exact=6*shell**2/(scale*point*block)
            gradient=-exact/scale*(1/point+2*(point-deadline)/block)
        derivative = (response(point+1e-5)-response(point-1e-5))/(2e-5*scale)
        assert abs(response(point)-exact)<1e-13 and abs(derivative-gradient)<1e-10
        cuts.append(dict(source_radius=shell, cut_radius=point,
                         availability_in_rs=available_time,
                         availability_us_3_solar=available_time*29.5529456858,
                         mean_field_times_rs=exact, radial_gradient_times_rs2=gradient))

    start = fully_on-.25
    duration = deadline-start

    def correlation(lag):
        end = deadline-lag
        if end <= start:
            return 0.
        points = sorted({x for x in [fully_on, fully_on-lag] if start<x<end})
        return quad(lambda t: source(t)*source(t+lag),start,end,
                    points=points,epsabs=3e-10)[0]

    def temporal_norm(shell):
        def kernel(lag):
            return 2*shell**2*correlation(lag)*log(abs(1-4*shell**2/lag**2))
        return quad(kernel,0.,duration,points=[.25,2*shell,duration-.25],
                    epsabs=3e-7,limit=120)[0]
    time_norm = temporal_norm(1.)

    def spectral_norm(box, dt, shell=1.):
        # Integrate the source with midpoint cells aligned to the receipt time.
        samples = int(np.ceil(duration/dt))
        step = duration/samples
        size = int(np.ceil(box/step))
        t = start+(np.arange(samples)+.5)*step
        k = 2*pi*np.fft.rfftfreq(size,d=step)
        transform = step*np.fft.rfft(source(t),n=size)
        integrand = np.zeros_like(k)
        integrand[1:] = 4*shell**2*np.sin(k[1:]*shell)**2/k[1:]*abs(transform[1:])**2
        # Smooth low-frequency endpoint correction for trapezoidal integration.
        dk=k[1]
        return np.trapezoid(integrand,dx=dk)+dk**2*shell**4*abs(transform[0])**2/3

    spectral = [spectral_norm(box,dt) for box,dt in [(160.,.0025),(320.,.00125)]]
    assert abs(spectral[-1]-time_norm)<2e-5
    error_prob=exp(-time_norm)/(2*(1+sqrt(-expm1(-time_norm))))
    inner_norm=temporal_norm(.5)
    independent=spectral_norm(320.,.00125,.5)
    assert abs(inner_norm-independent)<2e-5
    return dict(cuts=cuts, spectrum_norm=spectral, time_norm=time_norm,
                half_radius_source=dict(time_norm=inner_norm,spectral_norm=independent,
                                        one_sided_error_floor=exp(-inner_norm)),
                scalar_only_equal_prior_error=error_prob, one_sided_error_floor=exp(-time_norm),
                compactness=compactness, comoving_deadline=deadline)


def schwarzschild_return(sample=None):
    # Join the two optical null coordinates on the moving surface of the dust star.
    # Propagate only the scattered part. The direct delta-shell pulse is integrated analytically.
    deadline=-2*2**.25
    fully=-2*sqrt(6.)
    start=fully-.25
    shell=.5
    ramp=solve_ivp(lambda t,v:[6*shell*smooth_on((t-start)/.25)/t**2],
                   (start,fully),[0.],rtol=2e-12,atol=3e-15,dense_output=True)
    assert ramp.success
    def primitive(t):
        t=np.asarray(t)
        ans=np.zeros_like(t)
        smooth=(start<t)&(t<fully)
        if np.any(smooth):
            ans[smooth]=ramp.sol(t[smooth])[0]
        late=t>=fully
        ans[late]=ramp.y[0,-1]+6*shell*(1/fully-1/t[late])
        return ans
    def direct(t,x):
        return .5*(primitive(t-np.abs(x-shell))-primitive(t-x-shell))
    def potential(t,x):
        out=t-x+1
        inc=t+x-1
        f=out**3/12-out**2/4+out-2*np.log(-(out+2)/2)
        g=inc**3/12+inc**2/4+inc+2*np.log(-(inc-2)/2)
        r=1+wrightomega((g-f)/2-1)
        return out**3/(4*(out+2))*inc**3/(4*(inc-2))*(1-1/r)/r**3

    rows=[]
    for n in [64,128,256,512]:
        h=1/n
        steps=int(np.ceil((deadline-start)/h))+2
        x=np.arange(n+steps+6)*h
        prev=np.zeros_like(x)
        curr=np.zeros_like(x)
        gradients=[]
        for j in range(steps+1):
            t=deadline+(j-steps)*h
            if sample is not None:
                sample(n, t, h, curr, direct)
            if t>=fully+1+shell-h*1e-10:
                idx=np.array([n,n-1,n-2])
                full=curr[idx]+direct(t,x[idx])
                derivative=(3*full[0]-4*full[1]+full[2])/(2*h)
                gradients.append((derivative-full[0])/(t*t/4)**2)
            if j==steps:
                break
            nxt=np.zeros_like(x)
            nxt[1:-1]=curr[2:]+curr[:-2]-prev[1:-1]
            # No point beyond this past cone can influence the result at the stellar edge.
            ext=slice(n,n+steps-j+1)
            V=potential(t,x[ext])
            V[0]*=.5
            nxt[ext]-=h*h*V*(curr[ext]+direct(t,x[ext]))
            prev,curr=curr,nxt
        rows.append(dict(cells_per_star_radius=n,deadline_interior_edge_gradient=gradients[-1],
                         least_negative_sampled_gradient=max(gradients),
                         most_negative_sampled_gradient=min(gradients),
                         final_scattered_reduced_field=float(curr[n])))
    assert all(row["least_negative_sampled_gradient"]<0 for row in rows)
    eps=abs(rows[-1]["deadline_interior_edge_gradient"]-rows[-2]["deadline_interior_edge_gradient"])
    assert eps<3e-5
    horizon_scaling=abs(potential(deadline,np.array([1.]))[0]-4/deadline**2)
    assert horizon_scaling<5e-15
    return dict(transparent_edge_gradient=-(6*shell**2/(deadline**2/4)**2)*
                (1/((1-deadline)**2-shell**2)+2*(1-deadline)/((1-deadline)**2-shell**2)**2),
                geometric_matching_error=horizon_scaling,grids=rows)


def shield():
    # Primitive of a finite smooth pulse. The half-line Green function uses its differences.
    def primitive(t):
        return smooth_on(t/1.35)
    def response(t,r,L,P):
        return .5*(P(t-abs(r-L))-P(t-r-L))
    def inner(t):
        return primitive(t)+primitive(t-2.)
    def outer(t):
        return -primitive(t-1.)
    inside=outside=signal=0.
    times=np.linspace(-1.,10.,801)
    for radius in np.linspace(.04,3.1,103):
        field=response(times,radius,1.,inner)+response(times,radius,2.,outer)
        if radius<1.:
            single=response(times,radius,1.,primitive)
            inside=max(inside,np.max(abs(field-single)))
            signal=max(signal,np.max(abs(field)))
        if radius>2.:
            outside=max(outside,np.max(abs(field)))
    freq=np.linspace(.01,12.,601)
    form=np.sin(freq)*(1+np.exp(2j*freq))-np.sin(2*freq)*np.exp(1j*freq)
    assert max(inside,outside,np.max(abs(form)))<4e-15 and signal>.35
    return dict(interior_error=inside,exterior_error=outside,
                exterior_frequency_error=float(np.max(abs(form))),max_interior_radial_field=signal)


def surface():
    radius=4.
    initial=.85
    intake=.31
    release=.22
    def coefficients(m,r=radius):
        speed=sqrt(2*m/r)
        return np.array([-speed,-1.])/(r-2*m)
    def K(m):
        return 1/(radius*(1-sqrt(2*m/radius)))
    def derivative(m):
        s=sqrt(2*m/radius)
        return 1/(radius**2*s*(1-s)**2)
    def step(m,d,j):
        direction=(1,-1)[j]
        return quad(lambda x: coefficients(m+direction*x)[j],0.,d)[0]
    first=step(initial,intake,0)+step(initial+intake,release,1)
    second=step(initial,release,1)+step(initial-release,intake,0)
    curvature=quad(lambda x: quad(lambda y:derivative(initial+x-y),
                                  0,release)[0],0,intake)[0]
    assert abs(first-second+curvature)<1e-14

    def charges(t):
        return np.array([.30*t+.10*sin(t),.30*t-.10*sin(t)])
    def currents(t):
        return np.array([.30+.10*np.cos(t),.30-.10*np.cos(t)])
    def mass(t):
        return initial+np.diff(charges(t))[0]*(-1)
    def rate(t,b):
        return coefficients(mass(t))@currents(t)
    path=solve_ivp(rate,(0,2*pi),[0.],rtol=2e-12,atol=1e-13,dense_output=True)
    assert path.success
    pressure_error=energy_error=momentum_error=0.
    for time in np.linspace(0,2*pi,129):
        m=mass(time)
        I,O=currents(time)
        s=sqrt(2*m/radius)
        z=sqrt(1-s*s)
        q=1/z
        # Each current is independently converted to local density in units 4 pi G R^2=1.
        kd=q*s
        densities=np.array([I/kd,O/q])
        stress=densities @ np.array([kd**2,q**2])
        energy_current=densities @ np.array([-q*kd,q*q])
        pressure_error=max(pressure_error,abs(q*stress+radius*rate(time,0)))
        energy_error=max(energy_error,abs(I-O+z*energy_current))
        momentum=.013
        qd=q-momentum*derivative(m)*O
        qr=q-momentum*derivative(m)*I
        momentum_error=max(momentum_error,abs(qd*I-qr*O-q*(I-O)))
    t=pi/2
    assert max(pressure_error,energy_error,momentum_error)<2e-14
    assert abs(path.y[0,-1]+quad(lambda t:K(mass(t))*currents(t)[0],0.,2*pi)[0])<2e-10
    # Gaussian wavefunctions integrated directly against their translations.
    overlap_rows=[]
    for sigma in [.01,.03,.1]:
        shift=first-second
        overlap=quad(lambda b: exp(-(b*b+(b-shift)**2)/(4*sigma**2))
                     /(sqrt(2*pi)*sigma),-1.,1.,epsabs=1e-13)[0]
        assert abs(overlap-exp(-shift**2/(8*sigma**2)))<2e-14
        overlap_rows.append(dict(width=sigma,overlap=overlap,reference_fidelity=(1+overlap)/2))
    return dict(intake_first=first,release_first=second,curvature_area=curvature,
                order_difference=first-second,cycle_memory=float(path.y[0,-1]),
                zero_net_pressure_force=-radius*rate(t,0),residual_pressure=pressure_error,
                residual_energy=energy_error,residual_clock_power=momentum_error,
                gaussian=overlap_rows)


def vary_surface():
    # Vary every field in the spherical action before imposing the surface equations.
    nodes,weights=np.polynomial.legendre.leggauss(64)
    t=(nodes+1)/2
    weights=weights/2
    bump=t**2*(1-t)**2
    dbump=2*t*(1-t)*(1-2*t)
    values=np.array([4+.1*t, .20*t+.04*t**2, .12*t+.03*t**2,
                     1.2*t+.13*t**2, 1.4*t-.12*t**2, .1*np.sin(t),
                     .05+.02*t**2, 1+.04*t])
    speeds=np.array([0*t+.1, .2+.08*t, .12+.06*t, 1.2+.26*t, 1.4-.24*t,
                     .1*np.cos(t), .04*t, 0*t+.04])
    def action(v,w):
        R,I,O,Td,Tr,b,p,N=v
        Rp,Ip,Op,Tdp,Trp,bp,pp,Np=w
        m=.85+I-O
        s=np.sqrt(2*m/R)
        H=-R*np.sqrt(1-s*s)
        return weights@(I*Tdp-O*Trp-N*H+R*b*Rp+
                        p*(bp+(s*Ip+Op)/(R-2*m)))
    R,I,O,Td,Tr,b,p,N=values
    Rp,Ip,Op,Tdp,Trp,bp,pp,Np=speeds
    m=.85+I-O
    s=np.sqrt(2*m/R)
    q=1/np.sqrt(1-s*s)
    h=R-2*m
    ai,ao=-s/h,-1/h
    ar_i,ar_o=s/(2*R*h)+s/h**2,1/h**2
    curvature=-1/(R**2*s*(1-s)**2)
    expected=np.array([N*(q+1/q)/2-R*bp-p*(ar_i*Ip+ar_o*Op),
                       Tdp-N*q+pp*ai+p*(ar_i*Rp-curvature*Op),
                       -Trp+N*q+pp*ao+p*(ar_o*Rp+curvature*Ip),
                       -Ip,Op,R*Rp-pp,bp-ai*Ip-ao*Op,R/q])
    names=["radius","intake","emission","dust_clock","null_clock","memory","conjugate","lapse"]
    errors={}
    for j,name in enumerate(names):
        dv=np.zeros_like(values)
        dw=np.zeros_like(speeds)
        dv[j]=bump
        dw[j]=dbump
        eps=2e-5
        finite=(action(values+eps*dv,speeds+eps*dw)-action(values-eps*dv,speeds-eps*dw))/(2*eps)
        errors[name]=abs(finite-weights@(expected[j]*bump))
    assert max(errors.values())<2e-10
    return errors


def loaded_surface():
    # Linearized one-sided normal equation, a passive wave load and the mass constraint.
    radius=4.
    z=sqrt(1-2*.85/radius)
    inertia=.8
    results=[]
    for spring,impedance in [(0.,1.),(.7,2*sqrt(inertia*(.7+radius*z))),(.7,5.)]:
        effective=spring+radius*z
        def evolve(t,X):
            b1,v1,w1,b2,v2,w2,heat,area=X
            return np.array([w1,-z*w1,(radius*v1-spring*b1-impedance*w1)/inertia,
                             w2,-z*w2,(radius*v2-spring*b2-impedance*w2)/inertia,
                             z*impedance*w1**2,impedance*(b1*w2-w1*b2)])
        # Two compatible independent small displacements of the C=0 mode, at unit scale.
        data=[1.,-z,0.,0.,0.,1/inertia,0.,0.]
        end=solve_ivp(evolve,(0.,100.),data,method="DOP853",rtol=6e-12,atol=2e-13)
        assert end.success
        b,v,w,bb,vv,ww,E,W=end.y
        reconstructed=z*(inertia*w*w+spring*b*b)/2+radius*v*v/2
        err=max(abs(reconstructed+E-z*effective/2))
        assert err<8e-11 and abs(W[-1]-1)<3e-11
        assert max(abs(b[-1]),abs(v[-1]),abs(w[-1]))<1e-10
        results.append(dict(spring=spring,impedance=impedance,radiated_mass=E[-1],
                            symplectic_area=W[-1],mass_balance_error=err))
    return results


def elastic_readout():
    # Four independent canonical perturbations radiate through a single ordinary scalar.
    R=4.
    z=sqrt(1-2*.85/R)
    mass=R/z
    mu,k,Z=.8,.7,1.1
    tension=.22
    gas=2*tension*R**3
    stiffness=6*tension
    system=np.array([[0,1.,0,0],[-stiffness/mass,0,0,-R/mass],
                     [0,0,0,1.],[0,R/mu,-k/mu,-Z/mu]])
    rates=np.linalg.eigvals(system)
    assert max(rates.real)<0
    energy=np.diag([stiffness,mass,k,mu])
    omega=np.array([[0.,mass,R,0.],[-mass,0,0,0],[-R,0,0,mu],[0,0,-mu,0]])
    def derivatives(t,state):
        flow,radiated,sympl=state.reshape((3,4,4))
        b,w=flow[2],flow[3]
        return np.array([system@flow,2*Z*np.outer(w,w),
                         Z*(np.outer(b,w)-np.outer(w,b))]).ravel()
    end=solve_ivp(derivatives,(0.,25/abs(max(rates.real))),
                  np.array([np.eye(4),np.zeros((4,4)),np.zeros((4,4))]).ravel(),
                  method="DOP853",rtol=7e-11,atol=3e-13)
    assert end.success
    flow,rad,observed=end.y[:,-1].reshape((3,4,4))
    em=np.max(abs(rad+flow.T@energy@flow-energy))
    om=np.max(abs(observed+flow.T@omega@flow-omega))
    assert max(em,om)<5e-9 and np.linalg.norm(flow)<3e-9
    return dict(geometry_mass=mass,equilibrium_radius=(gas/(2*tension))**(1/3),
                curvature=stiffness,amplitude_decay_rates=sorted(float(-x.real) for x in rates),
                max_energy_form_error=float(em),max_symplectic_form_error=float(om),
                remaining_response_norm=float(np.linalg.norm(flow)))


def balanced_annulus():
    # Finite stationary annulus with separately conserved dust and null luminosity.
    R,m0,L=4.,.85,.002
    def rhs(r,state):
        m,A=state
        F=1-2*m/r
        v=np.sqrt(1-A*A)
        return np.array([L*(1+1/v)/A**2,
                         A*(m+r*L*(1+v)/A**2)/(r*r*F)])
    ode=solve_ivp(rhs,(R,6.),[m0,sqrt(1-2*m0/R)],rtol=2e-12,atol=2e-14,dense_output=True)
    assert ode.success
    residual=[]
    for r in np.linspace(4.05,5.95,31):
        m,A=ode.sol(r)
        mp,Ap=rhs(r,[m,A])
        step=1e-4
        App=(rhs(r+step,ode.sol(r+step))[1]-rhs(r-step,ode.sol(r-step))[1])/(2*step)
        F=1-2*m/r
        Fp=2*m/r**2-2*mp/r
        residual.append(abs(F*(App/A+Ap/(r*A))+.5*Fp*(Ap/A+1/r)))
    assert max(residual)<2e-10
    return dict(outer_mass=ode.y[0,-1],outer_lapse=ode.y[1,-1],
                maximum_angular_Einstein_residual=max(residual))


def port():
    # s-wave on a Schwarzschild half-line. G=c=r_s=1 and cap length d=3.
    # Normalize a smooth local L2 cap profile, independently of its frequency transform.
    radius=sqrt(2)
    cap=3.
    points,weights=np.polynomial.legendre.leggauss(100)
    y=(points+1)*cap/2
    weights=weights*cap/2
    packet=np.sin(pi*y/cap)**2
    packet/=sqrt(weights@(packet*packet))

    def spectrum(k,rmax):
        val=np.sin(k*cap)/k
        der=np.cos(k*cap)
        def rhs(r,state):
            f=1-1/r
            v=f/r**3
            pos,mom=np.split(state,2)
            return np.concatenate((mom/f,(v-k*k)*pos/f))
        ode=solve_ivp(rhs,(radius,rmax),np.r_[val,der],rtol=1.5e-8,atol=1e-10,
                      method="DOP853")
        assert ode.success
        phi,dp=np.split(ode.y[:,-1],2)
        determinant=np.hypot(dp,k*phi)
        integral=(np.sin(k[:,None]*y)/k[:,None])@(weights*packet)
        return (2/pi)*(k*integral/determinant)**2,determinant

    checks=[]
    rows=None
    for count,rmax in [(301,30.),(601,65.)]:
        k=np.linspace(.001,9.001,count)
        density,det=spectrum(k,rmax)
        w=float(np.trapezoid(density,x=k))
        assert abs(w-1)<5e-5 and np.min(det)>0
        checks.append(dict(sample_count=count,outer_radius=rmax,radiated_norm=w,
                           minimum_sampled_jost=float(np.min(det))))
        rows=(k,density)
    # Exact free continuation on the final characteristic. The tail has finite norm on any slice.
    late=[]
    for u in [1.,2.,5.,10.]:
        remaining=quad(lambda v: (1+v)**(-6),u,np.inf,epsabs=2e-13)[0]
        assert abs(remaining-1/(5*(1+u)**5))<1e-13
        late.append(dict(cut=u,residual_energy=remaining))
    # The reflected null coordinates give the position of a moving material end.
    rate=.5
    def extra_length(t):
        return .5*(t+expm1(-rate*t)/rate)
    lifetime=brentq(lambda t: extra_length(t)-cap,1.,10.)
    integrated=quad(lambda t:(1-exp(-rate*t))/2,0.,lifetime)[0]
    assert abs(integrated-cap)<1e-12
    return dict(cap_length=cap,radius=radius,stationary=checks,final_cone=late,
                hawking_duration_for_headroom_3rs=lifetime,
                added_depth_for_50rs=extra_length(50.)),rows


def figure(path, report, spectrum):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig,(ax,bx)=plt.subplots(1,2,figsize=(8.4,3),layout="constrained")
    t=np.linspace(-.5,6,401)
    p=lambda x:smooth_on(x/1.35)
    for r in [.65,1.55,2.45]:
        def wave(L,F):
            return .5*(F(t-abs(r-L))-F(t-r-L))
        u=wave(1.,lambda x:p(x)+p(x-2))+wave(2.,lambda x:-p(x-1))
        ax.plot(t,u,label=rf"$\chi/L={r:g}$")
    ax.set(xlabel="Conformal time / inner radius",ylabel="Reduced relative field")
    ax.legend(frameon=False,fontsize=8)
    bx.plot(*spectrum,color="#884628")
    bx.set(xlabel=r"Frequency $\omega r_s$",ylabel="Outgoing probability density",xlim=(0.,6.))
    fig.savefig(path)
    plt.close(fig)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--figure",type=Path)
    args=parser.parse_args()
    output,curve=port()
    report=dict(receipt=receipts(),schwarzschild=schwarzschild_return(),
                shield=shield(),surface=surface(),port=output,
                action_variations=vary_surface(),balanced_annulus=balanced_annulus(),
                loaded_surface=loaded_surface(),elastic_readout=elastic_readout())
    target=ROOT/"verification/mixed-flux-memory-results.json"
    target.write_text(json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf8")
    if args.figure:
        figure(args.figure,report,curve)
    print("Retarded source, mixed recoil and radiation port checks passed.")
