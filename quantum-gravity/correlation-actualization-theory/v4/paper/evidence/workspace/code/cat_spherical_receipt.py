"""Relational spherical collapse, a dust-sourced null loop, and a neutral material port.

All computations use dimensionless matrix units or Schwarzschild radius one.
No result is fitted to observational data. The fixed-background matter evolution
is exact in the indicated angular sector before collective quantum corrections.
"""
from fractions import Fraction
import json
from pathlib import Path

import numpy as np
from scipy import integrate, linalg, optimize, special

ROOT = Path(__file__).resolve().parents[1]
DELTA = .12
U0 = .50
V0 = .39
START = -1.18
G2 = .16


def tortoise(r):
    return r+np.log1p(-r)


def interior_radius(eta):
    # The principal Lambert branch gives the interior radius 0<r<1.
    return 1+special.lambertw(-np.exp(eta-1)).real


def axial_current_check():
    # A nonconstant comoving profile also tests the derivative along the dust.
    def current(v,r):
        h=r**(-.5)
        y=np.sqrt(r)
        # dQ/dr=1/[h(1+h)].
        Q=2*y**3/3-y*y+2*y-2*np.log1p(y)
        q=v+Q
        n=1+.2*np.sin(3*q)
        sigma=n/(h*r*r)
        return np.array([-sigma,sigma/(1+h)]),np.array([r*r*sigma/(1+h),-r*r*sigma*h])
    residual=0.
    for r in (.27,.33,.39):
        v=.23
        step=1.e-6
        Pv,c_v=(np.array(current(v+step,r))-np.array(current(v-step,r)))/(2*step)
        Pr,c_r=(np.array(current(v,r+step))-np.array(current(v,r-step)))/(2*step)
        y=np.sqrt(r)
        q=v+2*y**3/3-y*y+2*y-2*np.log1p(y)
        sigma=(1+.2*np.sin(3*q))/r**1.5
        predicted=.6*np.cos(3*q)/r-1.5*sigma/r
        residual=max(residual,abs(Pv[1]-Pr[0]-predicted),abs(c_v[0]+c_r[1]))
    assert residual<1e-7
    return residual


def dust_diamond(n,matter):
    ell=2
    lag=ell*(ell+1)
    angular=lag-2
    ri,rf=.4,.25
    eta0=tortoise(ri)
    duration=tortoise(rf)-eta0
    mesh=np.linspace(0,duration,n+1)
    dt=duration/n
    midpoint=(mesh[:-1]+mesh[1:])/2
    def geometry(axis):
        r=interior_radius(eta0+(axis[:,None]+axis[None,:])/2)
        f=1-1/r
        return r,f,f*(lag/r**2-3/r**3)
    r,f,V=geometry(midpoint)
    source=3*(-f)/(angular*r**1.5) if matter else np.zeros_like(r)
    wave=np.zeros((n+1,n+1))
    if not matter:
        wave[0,:]=np.sin(np.pi*mesh/duration)**4
    b=dt**2*V/16
    drive=dt**2*source/4
    for i in range(n):
        for k in range(n):
            wave[i+1,k+1]=((1+b[i,k])*(wave[i+1,k]+wave[i,k+1])
                            -(1-b[i,k])*wave[i,k]+drive[i,k])/(1-b[i,k])
    W=(wave[:-1,:-1]+wave[1:,:-1]+wave[:-1,1:]+wave[1:,1:])/4
    integrand=(V*W+source)/4
    du=np.sum(integrand[-1])*dt
    dv=np.sum(integrand[:,-1])*dt
    holonomy=angular*np.sum((-f)*W/r**3)*dt**2/4
    # Independent iteration of the causal integral on its nodes.
    node_r,node_f,node_V=geometry(mesh)
    node_source=3*(-node_f)/(angular*node_r**1.5) if matter else np.zeros_like(node_r)
    data=np.repeat(wave[0:1,:],n+1,axis=0)
    iterate=data.copy()
    for _ in range(8):
        phi=(node_V*iterate+node_source)/4
        along=integrate.cumulative_trapezoid(phi,dx=dt,axis=0,initial=0)
        iterate=data+integrate.cumulative_trapezoid(along,dx=dt,axis=1,initial=0)
    scale=max(1.,abs(wave[-1,-1]))
    assert abs(iterate[-1,-1]-wave[-1,-1])<2.e-3*scale
    f0=1-1/ri
    minQ=3*(-f0)/(angular*ri**1.5)
    minV=(-f0)*(3-lag*ri)/ri**3
    if matter:
        lb=minQ*duration**2/4
        gradient_lb=minQ*duration/4
        loop_lb=angular*(-f0)*minQ*duration**4/(64*ri**3)
    else:
        lb=0.
        gradient_lb=(3/8)*minV*duration/4
        loop_lb=0.
    assert wave[-1,-1]>lb and du>gradient_lb and holonomy>loop_lb
    return dict(mesh=n,source="dust" if matter else "incoming_pulse",coordinate_span=duration,
                psi=wave[-1,-1],psi_lower=lb,psi_causal_iterations=iterate[-1,-1],
                du_near_corner=du,dv_near_corner=dv,du_lower=gradient_lb,
                loop=holonomy,loop_lower=loop_lb,proper_time_remaining=2*rf**1.5/3)


def harmonic_test(ell,p):
    # The bounded Frobenius branch has b(0)=1, b'(0)=-ell(ell+1).
    lag=ell*(ell+1)
    c=[Fraction(1)]
    for n in range(12):
        pot=sum(c[i] for i in range(n-2)) if n>=3 else Fraction(0)
        c.append(((n*(n+1)-lag)*c[n]-Fraction(p)**2*pot)/(n+1)**2)
    def series(r,n):
        return sum(float(a)*r**i for i,a in enumerate(c[:n]))
    a=.002
    b=.019
    start=[series(a,12),sum(i*float(c[i])*a**(i-1) for i in range(1,12))]
    def rhs(r,z):
        field,der=z
        return [der,((lag-p*p*r**3/(r-1))*field-(2*r-1)*der)/(r*(r-1))]
    sol=integrate.solve_ivp(rhs,(a,b),start,rtol=3e-12,atol=3e-14,method='DOP853')
    assert sol.success and abs(sol.y[0,-1]-series(b,13))<3e-11
    return dict(ell=ell,killing_momentum=p,centre_slope=float(c[1]),
                field_at_test_radius=sol.y[0,-1],series_error=abs(sol.y[0,-1]-series(b,13)))


def corner_geometry(r):
    a=(1-r**4)**.25
    speed=a*a/r**2
    lapse_r=1/speed
    tau=integrate.quad(lambda y:y*y/np.sqrt(1-y**4),0,r,epsabs=1e-15)[0]
    return dict(r=r,a=a,misner_sharp_mass=1/(2*r**3),time_to_zero=tau,
                clock_over_cubic=tau/(r**3/3),inverse_radial_speed=lapse_r,
                density_times_8pi=-r**(-6))


def volume_correction_test(tension):
    """Evolve the angular waves with the necessary area relation imposed on coefficients."""
    lag=np.array([2.,6.])
    weights=lag/2
    amplitudes=np.array([.5,.5])
    quadratic=np.array([.3,-.1])
    # P(0)=1, sum w*b0*D=0: exhaust the adjustable quadratic coefficient.
    np.testing.assert_allclose(weights@(amplitudes*quadratic),0,atol=1e-16)
    def rhs(r,state):
        P=np.sqrt(1-r**4)
        inverse_A=r/((r*r-tension*P)*(r-1))
        values,flux=state[:2],state[2:]
        return np.r_[inverse_A*flux,lag*(1+tension*r*r/P)*values]
    sampled=np.array([.012,.006,.003,.0015])
    sol=integrate.solve_ivp(rhs,(0.,max(sampled)),np.r_[amplitudes,2*tension*quadratic],
                            method='DOP853',dense_output=True,rtol=2e-13,atol=1e-15)
    assert sol.success
    values=sol.sol(sampled)[:2]
    mismatch=(weights@(values*values)-np.sqrt(1-sampled**4))/sampled**3
    cubic=2*(weights@(lag*amplitudes**2))/(3*tension)
    assert abs(mismatch[-1]-cubic)<.004*abs(cubic)
    return dict(tension=tension,radii=sampled.tolist(),cubic_area_mismatch=mismatch.tolist(),
                limiting_coefficient=cubic)


def sphere(t):
    sn,cn,dn,_=special.ellipj(np.sqrt(2)*np.abs(t),.5)
    return cn,-np.sign(t)*np.sqrt(2)*sn*dn


def sphere_loss(t):
    """1-cn(sqrt(2)t|1/2) without cancellation near the turning point."""
    sn,cn,_,_=special.ellipj(np.sqrt(2)*abs(t),.5)
    return sn*sn/(1+cn)


def sphere_gap(t,k):
    # Exact addition formula for cn(x+y)-cn(x-y), with y=k/sqrt(2).
    sx,_,dx,_=special.ellipj(np.sqrt(2)*np.abs(t),.5)
    sy,_,dy,_=special.ellipj(abs(k)/np.sqrt(2),.5)
    return -np.sign(t*k)*2*sx*sy*dx*dy/(1-.5*sx*sx*sy*sy)


def scalar_transfer(j,ell,k,c,limit,check=False):
    C=np.sqrt(j*(j+1))
    rate=2*C*abs(sphere(k/2)[1])
    lag=ell*(ell+1)
    scaled_gap=((C*c*k)**2+lag*sphere(k/2)[0]**2)/rate
    def omega(s):
        t=s/np.sqrt(rate)
        if limit=='weber':
            return s*s+scaled_gap
        plus=sphere(t+k/2)[0]
        minus=sphere(t-k/2)[0]
        return ((C*sphere_gap(t,k))**2+(C*c*k)**2+lag*plus*minus)/rate
    boundary=6.
    frequency=np.sqrt(omega(-boundary))
    def rhs(s,w):
        return [w[1],-omega(s)*w[0]]
    start=np.array([1/np.sqrt(2*frequency),-1j*np.sqrt(frequency/2)])
    opts=dict(rtol=2e-12 if check else 2e-10,atol=2e-14 if check else 2e-12,method='DOP853')
    sol=integrate.solve_ivp(rhs,(-boundary,boundary),start,**opts)
    assert sol.success
    v,d=sol.y[:,-1]
    wronskian=-2*np.imag(v.conjugate()*d)
    assert abs(wronskian-1)<6e-8
    weight=abs((frequency*v-1j*d)/np.sqrt(2*frequency))**2
    return dict(j=j,ell=ell,k=k,flux=c,gap=scaled_gap,weight=weight,
                infinite_weber=np.exp(-np.pi*scaled_gap),wronskian_error=abs(wronskian-1))


def body_shape():
    # The two noncommuting adjoint vectors of the receiving point carry their own motion.
    def rhs(s,q):
        u,v,du,dv=q
        return [du,dv,-4*v*v*u,-4*u*u*v]
    sol=integrate.solve_ivp(rhs,(0.,1.22),[U0,V0,0.,0.],dense_output=True,method='DOP853',
                            rtol=3e-13,atol=2e-15)
    assert sol.success
    def shape(x):
        u,v,du,dv=sol.sol(abs(x))
        return u,v,np.sign(x)*du,np.sign(x)*dv
    u,v,du,dv=shape(np.linspace(0.,1.2,201))
    energy=du**2+dv**2+4*u*u*v*v
    np.testing.assert_allclose(energy,4*U0**2*V0**2,rtol=3e-12,atol=2e-13)
    assert min(u)>.25 and min(v)>.1
    return shape


SHAPE=body_shape()
SX=np.array([[0,1],[1,0]],complex)
SZ=np.diag([1.,-1.])


def central_detuning(x,j,chi=0.):
    if j is None:
        return DELTA+chi-x*x
    amplitude=1+chi/j**(2/3)
    return DELTA+chi-j**(2/3)*amplitude*sphere_loss(amplitude*x/j**(1/3))


def contact(j,chi):
    def gap(x):
        return central_detuning(x,j,chi)+SHAPE(x)[0]
    root=optimize.brentq(gap,START,-.18,xtol=1e-14)
    grid=np.linspace(START,0,80)
    assert max(central_detuning(grid,j,chi)-SHAPE(grid)[0])<0
    return root


def carrier(j,chi,start,stop,method):
    def h(x):
        return central_detuning(x,j,chi)*SZ-SHAPE(x)[1]*SX
    if method=='ode':
        sol=integrate.solve_ivp(lambda x,y:-1j*h(x)@y,(start,stop),np.array([1.,0.],complex),
                                method='DOP853',rtol=2e-12,atol=2e-14)
        assert sol.success
        state=sol.y[:,-1]
    else:
        state=np.array([1.,0.],complex)
        n=500
        dt=(stop-start)/n
        x=start+(np.arange(n)+.5)*dt
        u=central_detuning(x,j,chi)
        v=SHAPE(x)[1]
        ang=np.hypot(u,v)
        co=np.cos(dt*ang)
        si=-1j*np.sin(dt*ang)/ang
        for z in range(n):
            a,b=state
            state=np.array([co[z]*a+si[z]*(u[z]*a-v[z]*b),
                            co[z]*b+si[z]*(-v[z]*a-u[z]*b)])
    np.testing.assert_allclose(np.vdot(state,state),1.,atol=7e-11)
    return state


def material(j,chi=0.,check=True):
    first=contact(j,chi)
    clock=[first,-.36,0.,-first]
    rows=[]
    for end in clock:
        state=carrier(j,chi,START,end,'ode')
        prob=float(abs(state[1])**2)
        if check:
            other=carrier(j,chi,START,end,'midpoint')
            np.testing.assert_allclose(state,other,atol=8e-6)
        rows.append(dict(scaled_clock=end,one_port_probability=prob,
                         probability_nonzero_charge=2*prob*(1-prob)))
    result=dict(j=j,event=rows)
    if j is not None:
        t=first/j**(1/3)
        a,da=sphere(t)
        r=np.sqrt(abs(da))
        tau=integrate.quad(lambda y:sphere(y)[0]*np.sqrt(abs(sphere(y)[1])),t,0.,epsabs=1e-15)[0]
        result.update(turn_to_contact_radius=r,time_to_centre=tau,
                      scaled_time_to_centre=tau*np.sqrt(j),scaled_contact_radius=r*j**(1/6))
    return result


def signed_recoil(j,half_width=.18,reading='interior',order=38):
    # Relational radius spread. Two oriented links are right-occupied initially.
    # A compact cos² amplitude keeps both contacts within the same clock chart.
    nodes,weights=np.polynomial.legendre.leggauss(order)
    density=weights*np.cos(np.pi*nodes/2)**4
    density/=sum(density)
    start,stop=[],[]
    signed=[]
    for y in half_width*nodes:
        first=contact(j,y)
        last=first if reading=='crossing' else -.36
        assert first<-.36
        state=carrier(j,y,START,last,'ode')
        a,b=state
        signed.append(b*a.conjugate())
        start.append(first)
        stop.append(last)
    signed=np.array(signed)
    prob=np.dot(density,abs(signed)**2)
    overlap=abs(np.dot(density,signed**2))/prob
    distance=np.sqrt(max(0.,1-overlap**2))
    return dict(width=half_width,reading=reading,probability_signed=2*prob,
                signed_pointer_overlap=overlap,optimal_sign_success=(1+distance)/2,
                contact_range=[min(start),max(start)])


def rotor_bound(j):
    C=2*j+1
    grid=np.linspace(START,.9,300)
    u,v,_,_=SHAPE(grid)
    amin=min(sphere(grid/j**(1/3))[0])
    # Entire two-excitation relative stabilizer-neutral sector, at frozen shapes.
    # Four fundamental colour slots give ||sum Q_A²|| <= 16N.
    harmonic=special.digamma(2*j+1)+np.euler_gamma
    sum_weights=2*harmonic+1/C-1
    off=8*G2*(C+2)/(j*amin**2)
    big=8*G2*sum_weights/(C*amin**2)
    point=G2/j**(2/3)*(1/min(u)**2+1/min(v)**2+1/min(u*u+v*v))
    time=(.9-START)/j**(1/3)
    return dict(j=j,offblock_energy_bound=off,sphere_energy_bound=big,point_energy_bound=point,
                two_particle_amplitude_error_upper=time*(off+big+point))


def radius_clock(x,j,chi):
    # The scalar part of {Y_i, i[A0,Y_i]}/(2 C_j²) is a a'.
    if j is None:
        return x
    amplitude=1+chi/j**(2/3)
    a,da=sphere(amplitude*x/j**(1/3))
    return -j**(1/3)*amplitude**3*a*da/2


def reading_in_matrix_spectrum(reading,j,chi):
    if j is None:
        return reading
    bracket=(-1.215,.05)
    reduced=sphere((1+chi/j**(2/3))*bracket[0]/j**(1/3))[0]
    assert 3*reduced**4>1
    return optimize.brentq(lambda x:radius_clock(x,j,chi)-reading,*bracket,xtol=2e-14)


def receiver_on_radius_clock(j):
    # Both preparation and readout occur at the same intrinsic readings in every component.
    nodes,weights=np.polynomial.legendre.leggauss(26)
    density=weights*np.cos(np.pi*nodes/2)**4
    density/=sum(density)
    amplitudes,starts,stops=[],[],[]
    for chi in .18*nodes:
        start=reading_in_matrix_spectrum(START,j,chi)
        stop=reading_in_matrix_spectrum(-.36,j,chi)
        first=contact(j,chi)
        assert start<first<stop<0
        a,b=carrier(j,chi,start,stop,'ode')
        amplitudes.append(b*a.conjugate())
        starts.append(start)
        stops.append(stop)
    amplitudes=np.array(amplitudes)
    prob=density@abs(amplitudes)**2
    overlap=abs(density@(amplitudes**2))/prob
    return dict(j=j,preparation_spectrum_range=[min(starts),max(starts)],
                readout_spectrum_range=[min(stops),max(stops)],signed_probability=2*prob,
                sign_success=(1+np.sqrt(1-overlap**2))/2)


def matrix_sector(j):
    """Test the unrestricted matrix equations and the invariant fermion sector."""
    n=2*j+1
    m=np.arange(j,-j-1,-1)
    raising=np.diag(np.sqrt((j-m[1:])*(j+m[1:]+1)),1)
    sy=np.array([[0,-1j],[1j,0]])
    spins=[(raising+raising.T)/2,(raising-raising.T)/2.0j,np.diag(m)]
    gamma=[np.kron(SZ,s) for s in (SX,sy,SZ)]+[np.kron(SX,np.eye(2))]
    t=-.45/j**(1/3)
    a,da=sphere(t)
    u,v,du,dv=SHAPE(-.45)
    u,v,du,dv=u*j**(1/3),v*j**(1/3),du*j**(2/3),dv*j**(2/3)
    d=j-DELTA*j**(1/3)
    empty=np.zeros((2,2))
    point=[empty,empty,d*np.eye(2)+u*SZ,v*SX]
    sphere_block=[a*z for z in spins]+[np.zeros((n,n))]
    matrices=[linalg.block_diag(big,little) for big,little in zip(sphere_block,point)]
    velocities=[linalg.block_diag(da*z,small) for z,small in zip(spins,(empty,empty,du*SZ))]
    velocities.append(linalg.block_diag(np.zeros((n,n)),dv*SX))
    acc=[linalg.block_diag(-2*a**3*z,w) for z,w in zip(spins,(empty,empty,-4*v*v*u*SZ))]
    acc.append(linalg.block_diag(np.zeros((n,n)),-4*u*u*v*SX))
    def comm(x,y):
        return x@y-y@x
    clock=sum((pos@vel+vel@pos) for pos,vel in
              zip(sphere_block[:3],[da*z for z in spins]))/(2*j*(j+1))
    clock_error=np.linalg.norm(clock-a*da*np.eye(n))
    eom=max(np.linalg.norm(z+sum(comm(y,comm(y,x)) for y in matrices))
            for z,x in zip(acc,matrices))
    gauss=np.linalg.norm(sum(comm(z,w) for z,w in zip(matrices,velocities)))
    carrier_matrix=sum(np.kron(g,np.kron(big,np.eye(2))-np.kron(np.eye(n),p.T))
                       for g,big,p in zip(gamma,sphere_block,point))
    # zeta up, physical spin up, highest angular weight, right port +
    # and zeta down with the same spin/weight, right port -.
    columns=np.eye(8*n)[:,[0,4*n+1]]
    reduced=-u*np.eye(2)+(j*a-d)*SZ-v*SX
    reduced_error=np.linalg.norm(carrier_matrix@columns-columns@reduced)
    index=[]
    for clock in (START,-.36,.95):
        amp=sphere(clock/j**(1/3))[0]
        gap=SHAPE(clock)[0]*j**(1/3)
        row=[]
        for position in (d+gap,d-gap):
            probe=sum(np.kron(s,amp*z-(position*np.eye(n) if k==2 else 0))
                      for k,(s,z) in enumerate(zip((SX,sy,SZ),spins)))
            levels=np.linalg.eigvalsh(probe)
            row.append(int(np.sign(levels).sum()/2))
        index.append(row)
    assert max(eom,gauss,reduced_error,clock_error)<2e-11 and index==[[0,0],[0,1],[0,0]]
    return dict(spin=j,unrestricted_eom_error=eom,gauss_error=gauss,
                restricted_yukawa_error=reduced_error,clock_operator_error=clock_error,port_indices=index)


def common_time_impulse(half_width=.18):
    """Momentum conjugate to the initial radius displacement on each signed outcome."""
    nodes,weights=np.polynomial.legendre.leggauss(40)
    density=weights*np.cos(np.pi*nodes/2)**4
    norm,impulse,derivative_error=0.,0.,0.
    for chi,weight in zip(half_width*nodes,density):
        def rhs(x,y):
            h=central_detuning(x,None,chi)*SZ-SHAPE(x)[1]*SX
            a,da=y[:2],y[2:]
            return -1j*np.r_[h@a,h@da+SZ@a]
        sol=integrate.solve_ivp(rhs,(START,-.36),[1.+0j,0,0,0],method='DOP853',
                                rtol=2e-12,atol=2e-14)
        assert sol.success
        a,b,da,db=sol.y[:,-1]
        z=b*a.conjugate()
        dz=db*a.conjugate()+b*da.conjugate()
        norm+=weight*abs(z)**2
        impulse+=weight*np.imag(z.conjugate()*dz)
        if abs(chi)>.179:
            step=1e-5
            diff=(carrier(None,chi+step,START,-.36,'ode')-
                  carrier(None,chi-step,START,-.36,'ode'))/(2*step)
            derivative_error=max(derivative_error,np.linalg.norm(diff-[da,db]))
    assert derivative_error<1e-8 and impulse>0
    return dict(scaled_clock=-.36,width=half_width,conditional_momentum_plus=impulse/norm,
                conditional_momentum_minus=-impulse/norm,derivative_error=derivative_error,
                force_charge_covariance_over_2j=2*norm/sum(density))


def junction(r,y):
    x=np.sqrt(1/r-1)
    # Compute the surface tensor directly from the jump in both curvatures.
    jump_theta=(-y+x)/r
    jump_parallel=((1+y*y)/y-(1+x*x)/(2*x))/r
    angular=-r*(jump_parallel+jump_theta)
    longitudinal=-2*r*jump_theta
    np.testing.assert_allclose(angular,(1-x*x)/(2*x)-1/y,atol=3e-14)
    return dict(join_radius=r,core_speed=y,angular_stress_times_8pi_r=angular,
                longitudinal_stress_times_8pi_r=longitudinal)


def main():
    dust=[[dust_diamond(n,kind) for n in (70,140,280)] for kind in (True,False)]
    for seq in dust:
        assert abs(seq[-1]['psi']-seq[-2]['psi'])<.0001
    harmonics=[harmonic_test(l,p) for l in (1,2,3) for p in (0,2)]
    core=[corner_geometry(r) for r in (.5,.25,.125,.0625)]
    scalar=[]
    for j in (512,4096,32768):
        for ell,z in ((0,0.),(1,.45),(int(.27*np.sqrt(j)),.25)):
            args=(j,ell,.36,z/j**.5)
            original=scalar_transfer(*args,'matrix')
            approx=scalar_transfer(*args,'weber')
            precise=scalar_transfer(*args,'matrix',check=True)
            np.testing.assert_allclose(original['weight'],precise['weight'],rtol=4e-8,atol=3e-10)
            scalar.append(dict(matrix=original,finite_window_weber=approx['weight']))
    receipts=[material(j) for j in (64,512,4096,32768,2**24,None)]
    recoil=[signed_recoil(None,w,lab) for w in (.06,.18) for lab in ('crossing','interior')]
    extra=signed_recoil(None,.18,order=52)
    np.testing.assert_allclose(recoil[-1]['optimal_sign_success'],extra['optimal_sign_success'],atol=1e-11)
    gauge=[rotor_bound(j) for j in (4096,2**24,2**36,2**48)]
    shells=[junction(r,y) for r in (.12,.5,.8) for y in (.7,2.5)]
    return dict(dust_balance_residual=axial_current_check(),diamonds=dust,regular_harmonics=harmonics,
                zero_area=core,transverse_modes=scalar,material_receipts=receipts,conditional_recoil=recoil,
                collective_gauss_bounds=gauge,matrix_checks=[matrix_sector(j) for j in (3,8)],
                conditional_impulse=common_time_impulse(),matched_shells=shells,
                volume_area_test=[volume_correction_test(k) for k in (-.8,.8)],
                intrinsic_clock_receipts=[receiver_on_radius_clock(j) for j in (4096,32768,2**24,None)])


if __name__=='__main__':
    target=ROOT/'verification'/'cat-spherical-receipt-results.json'
    target.write_bytes((json.dumps(main(),indent=2,allow_nan=False)+'\n').encode('utf8'))
