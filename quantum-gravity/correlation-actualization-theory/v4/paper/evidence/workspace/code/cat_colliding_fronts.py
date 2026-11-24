"""CAT matrix fronts, finite-time vacuum correlations and work on a receiving block.

All coordinates below are spectral readings in the selected matrix state.  The unit
probe is a complex transverse link.  Integrals at fixed shifts have continuum
normalization per transverse spectral sector.
"""
from pathlib import Path
import json
from fractions import Fraction
from math import comb

import numpy as np
from scipy import integrate, optimize, special


ROOT = Path(__file__).resolve().parents[1]
CROSSING = 1.95
SPEED = -.4
AXIAL = .10
TRANSVERSE = np.sqrt(.15**2-AXIAL**2)
AMPLITUDE = .5


def shape(x, memory):
    s = np.clip(x, -1., 1.)
    if memory:
        return .5 + 35/32*(s-s**3+3*s**5/5-s**7/7)
    return (1-s*s)**4


class Front:
    def __init__(self, shift, mass, width, amplitude, memory=True):
        self.mass = mass
        self.half_shift = abs(shift)/2
        self.width = width
        self.amplitude = amplitude
        self.memory = memory
        self.edge = width+self.half_shift
        self.joints = np.unique([-self.edge, -abs(width-self.half_shift),
                                 abs(width-self.half_shift), self.edge])
        self.fluence = self.integral(lambda x: self.difference(x)**2)
        self.shift_out = self.fluence/(2*mass**2)
        self.edge_clock = self.edge+self.shift_out

    def difference(self, x):
        h, w = self.half_shift, self.width
        return self.amplitude*(shape((x+h)/w,self.memory)-shape((x-h)/w,self.memory))

    def integral(self, func):
        return sum(integrate.quad(func,a,b,epsabs=2e-14,epsrel=2e-13)[0]
                   for a,b in zip(self.joints[:-1],self.joints[1:]))

    def axis(self, order):
        """Ordinary and rectified null axes, using piecewise polynomial quadrature."""
        z,w = np.polynomial.legendre.leggauss(order)
        x = np.concatenate([(a+b+(b-a)*z)/2 for a,b in zip(self.joints[:-1],self.joints[1:])])
        weights = np.concatenate([(b-a)*w/2 for a,b in zip(self.joints[:-1],self.joints[1:])])
        # Squared profiles are piecewise polynomials of degree at most sixteen.
        v,g = np.polynomial.legendre.leggauss(12)
        clocks = []
        offset = -self.shift_out
        for a,b in zip(self.joints[:-1],self.joints[1:]):
            sample = x[(x>a)&(x<b)]
            sub = (sample[:,None]+a+(sample[:,None]-a)*v)/2
            partial = (sample-a)*((self.difference(sub)**2)@g)/2
            clocks.extend(sample+offset+partial/self.mass**2)
            offset += (b-a)*np.dot(g,self.difference((b+a+(b-a)*v)/2)**2)/(2*self.mass**2)
        np.testing.assert_allclose(offset,self.shift_out,atol=5e-13)
        return x,np.array(clocks),weights*self.difference(x)**2


def spectral_mass(kt,kx):
    # The two point blocks of the paired-crossing receiver have stationary centres.
    return np.sqrt((kt+TRANSVERSE)**2+kx**2+AXIAL**2)


def exact_reference_fluence():
    """Integrate the squared, shifted degree-seven profiles with rational arithmetic."""
    q=Fraction
    coefficients=[q(1,2),q(35,32),0,-q(35,32),0,q(21,32),0,-q(5,32)]
    def shifted(shift):
        return [sum(coefficients[k]*comb(k,n)*shift**(k-n) for k in range(n,8))
                for n in range(8)]
    plus,minus=shifted(q(1,2)),shifted(-q(1,2))
    inner=[a-b for a,b in zip(plus,minus)]
    def integrate_square(poly,lo,hi):
        return sum(a*b*(hi**(k+l+1)-lo**(k+l+1))/(k+l+1)
                   for k,a in enumerate(poly) for l,b in enumerate(poly))
    # The right and left outer intervals have the same integral. u=t/5, height=1/2.
    return (2*integrate_square(plus,-q(3,2),-q(1,2))+integrate_square(inner,-q(1,2),q(1,2)))/20


def positive_bounds(kt=0.,kx=.2,width=.2,amplitude=AMPLITUDE,memory=True,order=18):
    m = spectral_mass(kt,kx)
    f = Front(kt-kx,m,width,amplitude,memory)
    g = Front(kt+kx,m,width,amplitude,memory)
    area = f.fluence*g.fluence/m**2
    # One outgoing normalized box in [m/4,m/2]. A negative-frequency in packet
    # of opposite momentum bounds the inclusive occupation of that output.
    omega = np.hypot(m,m/2)
    phase_frequency = omega+m/8
    products = [phase_frequency*d.edge_clock for d in (f,g)]
    assert max(products)<np.pi/2
    iterations = special.i0(np.sqrt(area))-1
    lower_amplitude = m/4*area*max(0.,np.prod(np.cos(products))-iterations)/(8*np.pi*omega)
    number = lower_amplitude**2
    U = CROSSING+f.shift_out
    V = CROSSING+g.shift_out
    zmax = m*np.sqrt((U+f.edge_clock)*(V+g.edge_clock))
    _,us,wa=f.axis(order)
    _,vs,wb=g.axis(order)
    z=m*np.sqrt((U-us[:,None])*(V-vs[None,:]))
    # Positivity applies inside the past of this receiver and for the chosen mass band.
    assert CROSSING>max(f.edge,g.edge)
    if zmax < .8:
        q=zmax**2/4
        minus_y=(2/np.pi)*((np.log(2/zmax)-.578)*(1-q)-q)
        assert minus_y>0
        analytic=area*(1-q)*minus_y/8
        # Higher retarded insertions and the variance of the sourced field are nonnegative.
        born_lower=np.einsum('i,ij,j->',wa,-special.j0(z)*special.y0(z),wb)/(8*m**2)
        assert born_lower>=analytic
    else:
        analytic=born_lower=None
    band_upper=(m/4)*area*special.i0(np.sqrt(area))/(8*np.pi*m)
    return dict(shifts=[kt,kx],mass=m,width=width,amplitude=amplitude,memory=memory,
                fluences=[f.fluence,g.fluence],interaction_integral=area,
                outgoing_packet_mean_lower=number,outgoing_packet_nonempty_lower=number/(1+number),
                selected_beta_squared_upper=band_upper**2,log10_selected_beta_squared_upper=2*np.log10(band_upper),
                maximum_bessel_argument=zmax,local_variance_elementary_lower=analytic,
                local_variance_retarded_lower=born_lower)


def characteristic(top,side,coefficient,du,dv):
    """Second-order characteristic evolution by the centred integral on each cell."""
    n,m=len(top),len(side)
    field=np.zeros((n,m),complex)
    field[:,0],field[0,:]=top,side
    gamma=coefficient*(du[:,None]*dv[None,:])/16
    for i in range(n-1):
        # Each update in this row depends on its new left neighbour.
        for k in range(m-1):
            c=gamma[i,k]
            field[i+1,k+1]=((1-c)*(field[i+1,k]+field[i,k+1])/(1+c)-field[i,k])
    return field


def polarized_step_bounds(width,amplitude,cosine):
    """Bounds for the two normalized packets. Both shifted steps have positive sign."""
    mass=.25
    front=Front(.2,mass,width,amplitude)
    first=2*abs(cosine)*(.2*amplitude)**2
    second=front.fluence**2/mass**2
    # The absolute residual integral is exact when the sign is constant.
    if cosine<=0:
        area=first+second
    elif amplitude**2<=2*cosine*mass**2:
        area=first-second
    else:
        raise ValueError("Selected step is outside the constant-sign domain")
    assert area>0
    omega=np.hypot(mass,mass/2)
    phase=(omega+mass/8)*front.edge_clock
    ordered=np.exp(area/4)
    lower=(mass/4)*area*max(0.,np.cos(phase)**2-(ordered-1))/(8*np.pi*omega)
    upper=(mass/4)*area*ordered/(8*np.pi*mass)
    return dict(width=width,height=amplitude,cosine=cosine,residual_integral=area,
                beta_squared_lower=lower**2,beta_squared_upper=upper**2,
                log10_bounds=[2*np.log10(lower),2*np.log10(upper)])


def propagate(n,cosine,p_in,p_out,amplitude=AMPLITUDE):
    """Independently solve the original and rectified wave equations on the diamond."""
    m=.25
    front=Front(.2,m,.2,amplitude)
    u=np.linspace(-front.edge,front.edge,n+1)
    centres=(u[1:]+u[:-1])/2
    z,w=np.polynomial.legendre.leggauss(10)
    f=front.difference(centres)
    samples=(u[1:,None]+u[:-1,None]+np.diff(u)[:,None]*z)/2
    jumps=np.diff(u)*(1+(front.difference(samples)**2)@w/(2*m**2))
    U=np.r_[-front.edge_clock,-front.edge_clock+np.cumsum(jumps)]
    np.testing.assert_allclose(U[-1],front.edge_clock,atol=2e-12)
    def waves(p,axes):
        om=np.hypot(m,p)
        return np.exp(-.5j*(om+p)*axes),np.exp(-.5j*(om-p)*axes)
    a,b=waves(p_in,U)
    left=a*b[0]
    bottom=b*a[0]
    direct_mass=m*m+f[:,None]**2+f[None,:]**2+2*cosine*f[:,None]*f[None,:]
    offset=2*cosine*f[:,None]*f[None,:]-(f[:,None]*f[None,:])**2/m**2
    A=1+(f/m)**2
    direct=characteristic(left,bottom,direct_mass,np.diff(u),np.diff(u))
    changed=characteristic(left,bottom,m*m+offset/(A[:,None]*A[None,:]),jumps,jumps)
    def average(y):
        return (y[:-1,:-1]+y[1:,:-1]+y[:-1,1:]+y[1:,1:])/4
    out1,out2=waves(p_out,(U[1:]+U[:-1])/2)
    coeff=-1j/(8*np.pi*np.sqrt(np.hypot(m,p_in)*np.hypot(m,p_out)))
    def overlap(mode):
        return coeff*np.einsum('i,ij,j->',out1*np.diff(u),mode*offset,out2*np.diff(u))
    beta=overlap(average(direct))
    zero_order=overlap(waves(p_in,(U[1:]+U[:-1])/2)[0][:,None]*
                       waves(p_in,(U[1:]+U[:-1])/2)[1][None,:])
    return dict(mesh=n,orientation_cosine=cosine,beta=[float(beta.real),float(beta.imag)],
                modulus=abs(beta),distorted_first_modulus=abs(zero_order),
                rectified_modulus=abs(overlap(average(changed))),
                field_comparison=float(np.max(abs(direct-changed))))


def curvature_edge(width,memory,amplitude=AMPLITUDE):
    def deriv(y):
        return 35/32*(1-y*y)**3 if memory else -8*y*(1-y*y)**3
    def second(y):
        return -105/16*y*(1-y*y)**2 if memory else -8*(1-y*y)**2*(1-7*y*y)
    y=optimize.brentq(lambda z:amplitude*deriv(z)/width-1,-1,-.6)
    acceleration=amplitude*second(y)/width**2
    return acceleration**2/27  # half the trace of the two affine tidal eigenvalues, F'=1


def local_correlation(n):
    """Backward retarded kernel and the positive norm of a field smeared in its causal past."""
    m=.25
    f=Front(.2,m,.2,AMPLITUDE)
    u=np.linspace(-f.edge,f.edge,n+1)
    du=np.diff(u)
    uc=(u[:-1]+u[1:])/2
    z,w=np.polynomial.legendre.leggauss(10)
    samples=uc[:,None]+du[:,None]*z/2
    jumps=du*(1+(f.difference(samples)**2)@w/(2*m**2))
    U=np.r_[-f.edge_clock,-f.edge_clock+np.cumsum(jumps)]
    midpoint=(U[1:]+U[:-1])/2
    X=CROSSING+f.shift_out
    free=.5*special.j0(m*np.sqrt((X-U[::-1])*(X-U[-1])))
    squares=f.difference(uc)**2
    potential=m*m+squares[:,None]+squares[None,:]
    response=characteristic(free,free,potential[::-1,::-1],du[::-1],du[::-1])[::-1,::-1].real
    full=(response[:-1,:-1]+response[:-1,1:]+response[1:,:-1]+response[1:,1:])/4
    measure=np.outer(du*squares,du*squares)*full/(2*m**2)
    separation=m*np.sqrt((X-midpoint[:,None])*(X-midpoint[None,:]))
    assert np.min(measure)>=0
    cross=np.sum(measure*(-special.y0(separation)/2))
    # Rapidity is integrated only up to the stated limits. The omitted term is positive.
    def norm_to(limit):
        t,weights=np.polynomial.legendre.leggauss(96)
        t*=limit
        a=np.exp(-.5j*m*np.exp(t[:,None])*midpoint)
        b=np.exp(-.5j*m*np.exp(-t[:,None])*midpoint)
        transformed=np.sum((a@measure)*b,axis=1)
        return limit*np.dot(weights,abs(transformed)**2)/(4*np.pi)
    norms=[norm_to(limit) for limit in (4.,5.,6.)]
    assert norms[0]<norms[1]<norms[2]
    return dict(mesh=n,cross_term=cross,positive_norm_by_rapidity=norms,
                variance_through_rapidity_six=cross+norms[-1])


def local_kernel_bounds():
    """Bounds on the difference of Wightman functions throughout the two contacts."""
    m=.25
    f=Front(.2,m,.2,AMPLITUDE)
    S=f.fluence**2/m**2
    # Both arguments lie in the free future, at 1.6<=t<=1.95 and |x|<=.1.
    largest=m*(CROSSING+.1+f.shift_out+f.edge_clock)
    smallest=m*(1.6-.1+f.shift_out-f.edge_clock)
    assert 0<smallest<largest<.8
    q=largest**2/4
    small=S*(1-q)*((np.log(2/largest)-.578)*(1-q)-q)/(4*np.pi)
    assert small>0
    mass_bound=S*special.i0(np.sqrt(S))/4
    density_bound=m*m*special.i0(np.sqrt(S))/4
    length=2*f.edge_clock
    # For |z|<1 the absolute Bessel series are bounded by exp(z²/4).
    future_bound=np.exp(q)*(np.log(2/smallest)+.578+q)/(2*np.pi)
    c=np.exp(.25)/(2*np.pi)
    logarithm_integral=2+length*max(0,np.log(length))
    bulk=mass_bound*c*(mass_bound*(np.log(2/m)+.578+.25)+
                       density_bound*length*logarithm_integral)
    upper=2*mass_bound*future_bound+bulk
    return small,upper


def recoil_bound():
    """Connected two-front contribution relative to the separate, calibrated pulses."""
    m=.25
    f=Front(.2,m,.2,AMPLITUDE)
    length=2*f.edge_clock
    radius=CROSSING+.2+f.shift_out+f.edge_clock
    assert m*radius<1
    area=f.fluence**2/m**2
    mass=area*special.i0(np.sqrt(area))/4
    density=m*m*special.i0(np.sqrt(area))/4
    c=np.exp(.25)/(2*np.pi)
    constant=np.log(2/m)+.578+.25
    def absolute_integral(max_gap):
        return c*(mass*constant+density*length*(2+length*max(0,np.log(max_gap))))
    variance=2*absolute_integral(radius)+mass*absolute_integral(length)
    return dict(causal_variance_upper=variance,
                axial_shift_over_depth_upper=2*.16*(CROSSING+f.edge)**2*variance)


def grazing_parameters(j):
    half=.30*j**(-.6)
    sn,cn,dn,_=special.ellipj(np.sqrt(2)*half,.5)
    depth=j*sn**2/(1+cn)
    axial=2*depth
    transverse=np.sqrt(.15**2-axial**2)
    return half,depth,axial,transverse,j*np.sqrt(2)*sn*dn


def paired_contact(j):
    # The point is stationary. The same natural radial excursion puts it just
    # inside the sphere, then outside. No gate multiplies the Yukawa interaction.
    half,depth,axial,transverse,speed=grazing_parameters(j)
    mu=(j+1)/(.16*(j+2))
    bC=2*np.sqrt(j)+2
    hL=np.array([transverse-bC,.1,0.])
    hR=np.array([-bC,-.1,-axial])
    EL,ER=np.linalg.norm(hL),np.linalg.norm(hR)
    spin=np.sqrt((1+np.dot(hL,hR)/(EL*ER))/2)
    energy=mu*speed**2/2
    dt=2*half
    spread=np.sqrt(.16*half)   # optimal maximal free point width at the two ends
    # The smooth cosine envelope vanishes with three derivatives at its endpoints.
    derivative=4*np.pi/(2*.08*np.sqrt(7))
    error=dt*(2*derivative+EL+ER+2*depth)
    lower,upper=local_kernel_bounds()
    response=spin**2*lower-upper*(2*spin*error+error**2)
    return dict(log2_spin=int(np.log2(j)),half_duration=half,depth=depth,axial_offset=axial,
                second_point_stays_outside=bool(depth<axial),speed=speed,
                point_width_over_depth=spread/depth,spin_matrix_element=spin,
                ordinary_phase_budget=dt*(EL+ER),packet_drift_upper=error,
                normal_energy=energy,normal_energy_over_gap=energy/(EL+ER-.25),
                normal_energy_times_duration=energy*dt,window_inside_local_region=bool(dt<.02),
                excess_charge_coefficient_lower= max(0.,response) if dt<.02 else None)


def charge_indices(j):
    """Count both C2 ports in the full spin space across the two simple zeros."""
    half,depth,axial,_,_=grazing_parameters(j)
    labels=np.arange(-j,j+1)
    raising=np.diag(np.sqrt((j-labels[:-1])*(j+labels[:-1]+1)),-1)
    sx=np.array([[0,1],[1,0]])
    sy=np.array([[0,-1j],[1j,0]])
    sz=np.diag([1,-1])
    spin_y=(raising-raising.T)/(2.0j)
    D=np.kron(sx,(raising+raising.T)/2)+np.kron(sy,spin_y)
    D+=np.kron(sz,np.diag(labels))
    dL=-j+depth
    indices=[]
    minimum=[]
    for shift in (-2*half,0,2*half):
        w=special.ellipj(np.sqrt(2)*shift,.5)[1]
        charges=[]
        gaps=[]
        for point in (dL,dL-axial):
            spec=np.linalg.eigvalsh(w*D-point*np.kron(sz,np.eye(2*j+1)))
            charges.append(int(np.sum(spec>0)-(2*j+1)))
            gaps.append(float(np.sort(abs(spec))[1]))
        indices.append(charges)
        minimum.append(gaps)
    assert indices==[[0,0],[1,0],[0,0]] and np.min(minimum)>depth
    return dict(j=j,indices=indices,second_absolute_eigenvalue=minimum)


def bond_balance():
    # Compare the exact finite-shift exchange to the derivative of a bond flux.
    h=.1
    x=2*np.pi*(np.arange(64)+.5)/64
    mode=lambda a: np.sin(3*a)+.3*np.cos(7*a)
    density=lambda a: 1+.2*np.sin(2*a)
    difference=lambda f,a:f(a+h)-f(a-h)
    S=lambda a: density(a)*difference(mode,a)
    kernels=(lambda a:np.sin(a-.3),lambda a:3*np.cos(3*a)-2.1*np.sin(7*a))
    residuals=[]
    for f in kernels:
        g=lambda a:f(a)*S(a+h)+S(a)*f(a+h)
        exchange=f(x)*difference(S,x)+S(x)*difference(f,x)
        flux= lambda a:integrate.quad(g,a-h,a,epsabs=2e-14)[0]
        delta=1e-5
        derivative=np.array([(flux(a+delta)-flux(a-delta))/(2*delta) for a in x])
        assert np.max(abs(derivative-exchange))<2e-8
        assert abs(np.mean(exchange))<1e-14
        residuals.append(float(np.max(abs(derivative-exchange))))
    return residuals


def material_response(j,n,nt,nx):
    """Leading two-contact Yukawa response of a right occupied and left empty orbital.

    Time evolution of matter is unitary in every spatial Fourier mode. Integrating
    the adjoint retarded solution once gives the response of the entire spacetime
    smearing. No switch is inserted into the Hamiltonian at either end.
    """
    m=.25
    f=Front(.2,m,.2,AMPLITUDE)
    half,depth,axial,transverse,_=grazing_parameters(j)
    span=2*half
    centre=CROSSING-2*half
    dt=span/nt
    sigma_x=np.array([[0,1],[1,0]],complex)
    sigma_y=np.array([[0,-1j],[1j,0]])
    sigma_z=np.diag([1.,-1.])
    ident=np.eye(2)
    gp,gz,gb,gk,g9=(np.kron(sigma_x,ident),np.kron(sigma_y,ident),
                      np.kron(sigma_z,sigma_x),np.kron(sigma_z,sigma_y),np.kron(sigma_z,sigma_z))
    bC=2*np.sqrt(j)+2
    right_h=(0.-bC)*gb-.1*gk-axial*gz
    left_h=(transverse-bC)*gb+.1*gk
    # Choose an unambiguous vector in the doubly degenerate right occupied space.
    right=(np.eye(4)-right_h/np.linalg.norm(right_h,2))@np.array([1,0,0,0])
    right/=np.linalg.norm(right)
    left=(np.eye(4)+left_h/np.linalg.norm(left_h,2))@g9@right
    left/=np.linalg.norm(left)
    length=2.
    dx=length/nx
    x=dx*(np.arange(nx)-nx//2)
    p=2*np.pi*np.fft.fftfreq(nx,d=dx)
    envelope=np.where(abs(x)<.08,np.cos(np.pi*x/(2*.08))**4,0.)
    envelope/=np.sqrt(dx*np.sum(envelope**2))
    def prepare(spin):
        return np.fft.fft(envelope[:,None]*spin[None,:],axis=0,norm="ortho")
    L,R=prepare(left),prepare(right)
    def advance(state,t,bs,ks,ds,duration):
        sn,cn,_,_=special.ellipj(np.sqrt(2)*(t-centre),.5)
        lam=depth-j*sn**2/(1+cn)+ds
        mass_part=bs*gb+ks*gk+lam*gz
        eps=np.sqrt(bs**2+ks**2+lam**2+p**2)
        acted=p[:,None]*(state@gp.T)+state@mass_part.T
        return np.cos(duration*eps)[:,None]*state-1j*(np.sin(duration*eps)/eps)[:,None]*acted
    tx=[]; xx=[]; weights=[]
    leakage=0.
    for i in range(nt):
        t=centre-half+(i+.5)*dt
        L=advance(L,t-dt/4,transverse-bC,.1,0.,dt/2)
        R=advance(R,t-dt/4,-bC,-.1,-axial,dt/2)
        l=np.fft.ifft(L,axis=0,norm="ortho")
        r=np.fft.ifft(R,axis=0,norm="ortho")
        keep=abs(x)<=.08+(i+.5)*dt+2*dx
        leakage=max(leakage,dx*np.sum(abs(l[~keep])**2+abs(r[~keep])**2))
        overlap=np.sum(l.conj()*(r@g9.T),axis=1)
        tx.extend(np.full(np.count_nonzero(keep),t))
        xx.extend(x[keep])
        weights.extend(overlap[keep]*dx/nt)
        L=advance(L,t+dt/4,transverse-bC,.1,0.,dt/2)
        R=advance(R,t+dt/4,-bC,-.1,-axial,dt/2)
    np.testing.assert_allclose([dx*np.sum(abs(L)**2),dx*np.sum(abs(R)**2)],[1.,1.],atol=1e-12)
    assert leakage<1e-6
    tx=np.array(tx); xx=np.array(xx); weights=np.array(weights)
    xu,xv=tx-xx+f.shift_out,tx+xx+f.shift_out
    u=np.linspace(-f.edge,f.edge,n+1); du=np.diff(u)
    c=(u[1:]+u[:-1])/2
    z,w=np.polynomial.legendre.leggauss(10)
    jumps=du*(1+(f.difference(c[:,None]+du[:,None]*z/2)**2)@w/(2*m*m))
    U=np.r_[-f.edge_clock,-f.edge_clock+np.cumsum(jumps)]
    mid=(U[1:]+U[:-1])/2
    def future_kernel(us,vs,wightman=False):
        # Chunking bounds memory independently of the quadrature resolution.
        result=np.empty(len(us),complex)
        for i in range(0,len(us),64):
            sl=slice(i,i+64)
            arg=m*np.sqrt((xu[:,None]-us[None,sl])*(xv[:,None]-vs[None,sl]))
            J=special.j0(arg)
            if wightman:
                result[sl]=weights.conj()@((-special.y0(arg)-1j*J)/4)
            else:
                result[sl]=weights@(J/2)
        return result
    side=future_kernel(U[::-1],np.full_like(U,U[-1]))
    bottom=future_kernel(np.full_like(U,U[-1]),U[::-1])
    sq=f.difference(c)**2
    mass=m*m+sq[:,None]+sq[None,:]
    response=characteristic(side,bottom,mass[::-1,::-1],du[::-1],du[::-1])[::-1,::-1]
    full=(response[:-1,:-1]+response[:-1,1:]+response[1:,:-1]+response[1:,1:])/4
    measure=np.outer(du*sq,du*sq)*full/(2*m**2)
    rows,cols=np.meshgrid(mid,mid,indexing='ij')
    W=future_kernel(rows.ravel(),cols.ravel(),wightman=True).reshape(n,n)
    cross=2*np.sum(measure*W).real
    t,quad_w=np.polynomial.legendre.leggauss(100)
    t*=6.
    a=np.exp(.5j*m*np.exp(t[:,None])*mid)
    b=np.exp(.5j*m*np.exp(-t[:,None])*mid)
    pos=6*np.dot(quad_w,abs(np.sum((a@measure)*b,axis=1))**2)/(4*np.pi)
    leading_excess=.16*span**2*cross
    return dict(j=j,source_cells=n,time_steps=nt,spatial_points=nx,
                positive_cross_term=cross,positive_norm_through_rapidity_six=pos,
                normalized_excess_through_rapidity_six=cross+pos,
                leading_charge_weight_excess_lower=leading_excess,log10_leading_charge_weight_excess=np.log10(leading_excess),
                orbital_leakage=float(leakage))


def material():
    j=8
    sn,cn,dn,_=special.ellipj(np.sqrt(2)*(CROSSING+.225),.5)
    wall_speed=SPEED-j*np.sqrt(2)*sn*dn
    bC=2*np.sqrt(j)+2
    hL=np.array([TRANSVERSE-bC,.1,0.])
    hR=np.array([-bC,-.1,-AXIAL])
    EL,ER=np.linalg.norm(hL),np.linalg.norm(hR)
    mu=(j+1)/(.16*(j+2))
    radial_energy=mu*wall_speed**2/2
    spin=(1+np.dot(hL,hR)/(EL*ER))/2
    assert spin>.99 and radial_energy>EL+ER-.25 and abs(cn)>.4
    return dict(j=j,radius_at_crossing=cn,clock=CROSSING,oriented_level_speed=wall_speed,
                static_pair_threshold=EL+ER,available_scalar_mass=.25,spin_factor=spin,
                normal_inertia=mu,normal_kinetic_energy=radial_energy,
                point_sphere_magnetic_lower=(bC-TRANSVERSE)**2-2*j)


def main():
    baseline=positive_bounds()
    fluence=exact_reference_fluence()
    np.testing.assert_allclose(float(fluence),baseline['fluences'][0],rtol=2e-13)
    baseline['exact_fluence']=str(fluence)
    baseline['exact_interaction_integral']=str(16*fluence**2)
    refined=positive_bounds(order=30)
    np.testing.assert_allclose(refined['local_variance_retarded_lower'],baseline['local_variance_retarded_lower'],
                               rtol=2e-9)
    grid=[positive_bounds(kt,kx) for kt in (-.01,0.,.01) for kx in (.18,.2,.22)]
    comparisons=[]
    for cosine in (-1.,0.,1.):
        rows=[propagate(n,cosine,-.08,.09) for n in (80,160,320)]
        assert rows[-1]['field_comparison']<rows[0]['field_comparison']/5
        np.testing.assert_allclose(rows[-1]['modulus'],rows[-1]['rectified_modulus'],rtol=3e-6)
        comparisons.append(rows)
    narrow=[]
    fixed_energy=[]
    for width in (.05,.025,.0125,.00625):
        for memory in (True,False):
            a=positive_bounds(width=width,memory=memory)
            a['single_front_half_tidal_trace_where_derivative_one']=curvature_edge(width,memory)
            narrow.append(a)
            amplitude=AMPLITUDE*np.sqrt(width/.2)
            fixed=positive_bounds(width=width,amplitude=amplitude,memory=memory)
            gradient=(lambda s:35/32*(1-s*s)**3) if memory else (lambda s:-8*s*(1-s*s)**3)
            energy=amplitude**2/width*integrate.quad(lambda s:gradient(s)**2,-1,1)[0]
            fixed['gradient_energy']=energy
            fixed['single_front_half_tidal_trace_where_derivative_one']=curvature_edge(width,memory,amplitude)
            assert fixed['fluences'][0]<=2*width*energy*(.2+2*width)
            fixed_energy.append(fixed)
    for memory in (True,False):
        sequence=[row for row in fixed_energy if row['memory']==memory]
        np.testing.assert_allclose([row['gradient_energy'] for row in sequence],sequence[0]['gradient_energy'])
        assert sequence[0]['selected_beta_squared_upper']>sequence[-1]['selected_beta_squared_upper']
        assert sequence[0]['single_front_half_tidal_trace_where_derivative_one']<sequence[-1]['single_front_half_tidal_trace_where_derivative_one']
    angles=[]
    tuned=[]
    for width in (.05,.025,.0125,.00625,.003125,.0015625):
        for cosine in (-1.,0.,1.):
            angles.append(polarized_step_bounds(width,AMPLITUDE*np.sqrt(width/.2),cosine))
        for cosine in (-.5,.5):
            tuned.append(polarized_step_bounds(width,.25,cosine))
    ratio={cosine:[r['beta_squared_upper'] for r in angles if r['cosine']==cosine]
           for cosine in (-1.,0.,1.)}
    for cosine,exponent in ((-1.,2),(0.,4),(1.,2)):
        assert abs(np.log2(ratio[cosine][-2]/ratio[cosine][-1])-exponent)<.12
    assert tuned[-1]['beta_squared_upper']<tuned[-2]['beta_squared_lower']
    core=material()
    local=[local_correlation(n) for n in (100,200)]
    np.testing.assert_allclose(local[0]['variance_through_rapidity_six'],
                               local[1]['variance_through_rapidity_six'],rtol=1e-5)
    assert local[-1]['cross_term']>baseline['local_variance_retarded_lower']
    walls=[paired_contact(float(2**k)) for k in (8,20,40,80,120,160,200)]
    assert walls[-1]['excess_charge_coefficient_lower']>0
    receipts=[]
    for j in (8,128,2048,1048576,2**40):
        pair=[material_response(j,48,28,512),material_response(j,80,48,896)]
        np.testing.assert_allclose(pair[0]['positive_cross_term'],pair[1]['positive_cross_term'],rtol=.004)
        assert pair[1]['positive_cross_term']>0 and paired_contact(j)['second_point_stays_outside']
        receipts.append(pair)
    return dict(reference=baseline,sample_of_nearby_spectral_sectors=grid,independent_wave_solutions=comparisons,
                narrowing=narrow,narrowing_at_fixed_energy=fixed_energy,
                finite_energy_step_polarizations=angles,tuned_displacements=tuned,
                material=core,local_response=local,uniform_local_kernel=local_kernel_bounds(),
                paired_contacts=walls,charge_indices=[charge_indices(j) for j in (8,16)],
                local_yukawa_receipts=receipts,connected_recoil=recoil_bound(),
                bond_flux_finite_difference_residuals=bond_balance())


if __name__=='__main__':
    destination=ROOT/'verification'/'cat-colliding-fronts-results.json'
    destination.write_bytes((json.dumps(main(),indent=2,allow_nan=False)+'\n').encode('utf-8'))
