"""Causal resonance, parity scattering and received spin-two radiation in Schwarzschild."""
from functools import lru_cache
from math import acos, cos, degrees, exp, expm1, pi, sqrt
from pathlib import Path
import json

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import eigh
from scipy.optimize import brentq, minimize_scalar
from scipy.special import eval_jacobi, roots_legendre

from charged_horizon_receipts import charged_results, matrix_currents, primitive_source, soft_absorption
from gravitational_resonance_transfer import hydrogenic, transition
from natural_flux_endpoints import tensor_scattering

ROOT = Path(__file__).resolve().parents[1]


def coefficients(branch, mismatch):
    return 100*branch - 4*branch**2 + 48*mismatch*branch**2, 96*mismatch*branch**3


def moment_matrices(dimensionless_duration, cells):
    """Rayleigh--Ritz with orthonormal cell pulses; integrate both kernels exactly."""
    # v=Gamma*t/2, so u=1/(1+y^2) has kernel exp(-|v|)/2.
    width = dimensionless_duration/(2*cells)
    distance = np.arange(cells)*width
    # Two centered integrals of exp(-|t|) and (1+|t|) exp(-|t|)
    # per cell pair, divided by cell width. Use expm1 on diagonal.
    moment0 = 2*np.sinh(width/2)**2 / width
    moment1 = (2*width*np.sinh(width)-4*(np.cosh(width)-1)) / width
    kernel1 = np.exp(-distance)*moment0
    kernel2 = np.exp(-distance)*((1+distance)*moment0/2-moment1/4)
    kernel1[0] = (width+np.expm1(-width))/width
    kernel2[0] = (2*width-3+(width+3)*np.exp(-width))/(2*width)
    loc = abs(np.arange(cells)[:, None] - np.arange(cells))
    return kernel1[loc], kernel2[loc]


def top(a):
    n=len(a)
    return eigh(a, eigvals_only=True, subset_by_index=[n-1,n-1])[0]


def averaged_test(branch, mismatch, dimensionless_duration, cells, both=False):
    u,v=moment_matrices(dimensionless_duration,cells)
    c0,c2=coefficients(branch,mismatch)
    gain=c0*u-c2*v
    if not both:
        return top(gain)
    thin=coefficients(branch,0.)[0]*u
    def dual(mult):
        return top(gain-mult*thin)+25*mult
    sol=minimize_scalar(dual,bounds=(0.,4.),method="bounded",options={"xatol":1e-11})
    assert sol.success and sol.x<3.99
    return min(dual(0.),sol.fun)


def temporal_results():
    elastic = transition((3,2),(1,0),2/15)
    inelastic = transition((3,2),(2,0),2/15)
    total = elastic["width_over_G_mu3_alpha6"] + inelastic["width_over_G_mu3_alpha6"]
    b = elastic["width_over_G_mu3_alpha6"]/total
    thresholds = []
    for d in [0., 1/6, .25, .4, 1.]:
        root = lambda n: brentq(lambda t: averaged_test(b, d, t, n)-25, .2, 9.)
        coarse, fine = root(64), root(128)
        extrap = fine + (fine-coarse)/3
        assert abs(fine-coarse) < .00016
        thresholds.append([d, coarse, fine, extrap, 100/coefficients(b,d)[0]])
    joint=[]
    for d in [.25,.4]:
        limits=[brentq(lambda t: averaged_test(b,d,t,n,both=True)-25,1.,32.) for n in (64,128)]
        joint.append([d,*limits,limits[1]+(limits[1]-limits[0])/3])
    # Explicit pure packet: flat even part and opposite constant phases on its halves.
    h=2.5
    alpha=.137
    even_u=lambda t:(t+expm1(-t))/t
    even_v=lambda t:(2*t-3+(t+3)*exp(-t))/(2*t)
    U,V=[(2*alpha-1)*f(h)+2*(1-alpha)*f(h/2) for f in (even_u,even_v)]
    example=[coefficients(b,d)[0]*U-coefficients(b,d)[1]*V for d in [0.,.25]]
    assert example[0]<25<example[1]
    even=[even_u(h),even_v(h)]
    odd=[2*f(h/2)-f(h) for f in (even_u,even_v)]
    def score(d,mom):
        c,k=coefficients(b,d)
        return c*mom[0]-k*mom[1]
    target=(25-score(1/6,odd))/(score(1/6,even)-score(1/6,odd))
    common=np.array(even)*target+np.array(odd)*(1-target)
    conditioned=[target,score(2233/13644,common),score(473/2747,common)]
    assert conditioned[1]<25<conditioned[2]
    w = 4/9
    separation = (2**1.5-1)*2/3
    T = np.array([.01,.1,1.,4.,10.])
    cut = []
    for duration in T:
        h = duration/2
        # Same-window causal Volterra operator; unrestricted future Gram kernel.
        k1 = brentq(lambda z: z*cos(z)+h*np.sin(z), pi/2,pi)
        k2 = brentq(lambda z:z*np.tan(z/2)-h,1e-15,pi-1e-12)
        same = b**2*h**2/(h*h+k1*k1)
        late = b**2*h**2/(h*h+k2*k2)
        assert 0 < same < late < min(1., b*b*duration/4) and late < b*b
        cells=128
        cell=h/cells
        u,_=moment_matrices(duration,cells)
        ringdown=(-expm1(-cell))*np.exp(-cell*np.arange(cells-1,-1,-1))/sqrt(cell)
        verify_late=b*b*top(u)
        verify_same=b*b*top(u-np.outer(ringdown,ringdown)/2)
        assert abs(verify_late/late-1)<6e-5 and abs(verify_same/same-1)<6e-5
        cut.append([duration, same, late, b*(-expm1(-duration))])
    # Check the exact analytic cell integrals independently against quadrature.
    for h in [.01,.6]:
        for shift in [0.,h,2*h]:
            for power in [1,2]:
                f=lambda t: exp(-abs(t))/2 if power==1 else (1+abs(t))*exp(-abs(t))/4
                direct=quad(lambda t:(h-abs(t))*f(shift+t)/h,-h,h,points=[0])[0]
                if shift==0:
                    formula = (h+expm1(-h))/h if power==1 else (2*h-3+(h+3)*exp(-h))/(2*h)
                else:
                    f0=2*np.sinh(h/2)**2/h
                    f1=(2*h*np.sinh(h)-4*(np.cosh(h)-1))/h
                    formula=exp(-shift)*(f0 if power==1 else ((1+shift)*f0/2-f1/4))
                assert abs(direct-formula)<1e-12
    # Independent spectral test using the exact two moments at matched detuning.
    for d in [0.,1/6,.4]:
        u=1/(4*b)
        A,B=coefficients(b,d)
        assert abs(A*u-B*u*u-25-b*(6*d-1)) < 2e-14
    return dict(branch=b, onset_GammaT=thresholds, same_input_onset_GammaT=joint, explicit_pulse_scores=example, survival_calibrated_pulse=conditioned, finite_gate=cut,
                gamma_over_gap_per_Gmu2alpha4=total/w,
                infall_2rs_to_rs_over_rs=separation,
                gammaT_at_gap_rs_point7_per_Gmu2alpha4=separation*.7*total/w,
                tidal_mixing_at_horizon_gap_rs_point7=elastic["radial_integral"]*w/(10*.7**2))


@lru_cache(None)
def scattering(x, ell, radius=56., order=10):
    return tensor_scattering(x, radius, order, ell)


def polarization(x, ell):
    t, r = scattering(x, ell)
    angular=(ell-1)*ell*(ell+1)*(ell+2)
    phase=(angular+6j*x)/(angular-6j*x)
    flip=abs(r*(phase-1)/2)**2
    assert abs(abs(r)**2 + abs(t)**2-1) < 3e-9
    assert abs(flip-abs(r)**2*(6*x)**2/(angular**2+(6*x)**2)) < 6e-15
    return abs(t)**2, flip


def material_receipt():
    gg=transition((3,2),(1,0),2/15)["width_over_G_mu3_alpha6"]
    # Electric quadrupole / (mu alpha^7 delta^2), E1 / (mu alpha^5).
    ge=gg/4
    dip=quad(lambda r:r**3*hydrogenic(3,2,r)*hydrogenic(2,1,r),0.,np.inf)[0]
    e1=4/3*(2/5)*(5/72)**3*dip*dip
    # Verify the transverse E2 projection on a normalized real STF tensor.
    q=np.diag([-1.,-1.,2.])/sqrt(6.)
    def angular(c):
        n=np.array([sqrt(1-c*c),0.,c])
        return np.dot(q@n,q@n)-np.dot(n,q@n)**2
    assert abs(quad(angular,-1,1)[0]/2-.2)<1e-14
    identical=np.array([[sqrt(ge),sqrt(gg)],[sqrt(ge),sqrt(gg)]])
    conjugate=identical.copy()
    conjugate[1,0]*=-1
    assert abs(np.linalg.det(identical))<1e-15
    assert abs(np.linalg.det(conjugate)**2-4*ge*gg)<1e-15
    return dict(E2_per_mu_alpha7_delta2=ge,G2_per_G_mu3_alpha6=gg,E1_per_mu_alpha5=e1,
                E2_over_E1_per_alpha2_delta2=ge/e1,fluorescence_factor=80,
                isotropic_two_photon_leakage_at_s_over_E1E2_point01=.01/4)


def angular_image(x, largest=8):
    ells=np.arange(2,largest+1)
    weights=np.array([(2*l+1)*abs(scattering(x,int(l))[0])**2 for l in ells])
    def visibility(theta):
        c=cos(theta)
        return sum(weights*(((1+c)/2)**2)*eval_jacobi(ells-2,0,4,c))/sum(weights)
    # g=1/2 corresponds to d=1/6 for two tagged helicity labels.
    root=brentq(lambda theta: visibility(theta)-.5,0,pi)
    info=[visibility(a*pi/180) for a in [0.,30.,60.,90.,120.,180.]]
    return dict(x=x,first_crossing_degrees=degrees(root),quadrupole_fraction=weights[0]/sum(weights),
                last_partial_fraction=weights[-1]/sum(weights),real_visibility=info)


def horizon_profile(x, ell=2):
    """In-mode on a radial geodesic; r_s=1. Normalize to its horizon value."""
    L = ell*(ell+1)
    a1=(L-3)/(1-2j*x)
    a2=((L-1)*a1-2*L+9)/(4*(1-1j*x))
    radii=[2.,1.25,1.01,1.,.99,.8,.5]
    values={1.:(1.+0j,0.)}
    def equation(r, state):
        A, deriv, v = state
        f=1-1/r
        return (deriv, ((2j*x-r**-2)*deriv+(L/r**2-3/r**3)*A)/f,
                -sqrt(r)/(1+1/sqrt(r)))
    def solve_side(sign):
        dr=sign*1e-6
        group=sorted((r for r in radii if (r-1)*sign>0),reverse=sign<0)
        sol=solve_ivp(equation,(1+dr,group[-1]),[1+a1*dr+a2*dr**2,a1+2*a2*dr,-dr/2],
                      t_eval=group,method="DOP853",rtol=5e-12,atol=5e-14)
        assert sol.success
        for r,A,v in zip(group,sol.y[0],sol.y[2].real):
            values[r]=(A,v)
    solve_side(1)
    solve_side(-1)
    rows=[]
    for r in radii:
        A,v=values[r]
        curvature=A*np.exp(-1j*x*v)/r**6
        rows.append([r, 2*(1-r**1.5)/3, float(curvature.real),float(curvature.imag),float(abs(curvature)**2)])
    slope=6-a1-1j*x/2
    return dict(x=x,relative_curvature=rows,horizon_proper_log_derivative=[slope.real,slope.imag])


def darboux_test(x,ell):
    """Direct even and odd ODE propagation on the same finite interval."""
    L=ell*(ell+1)
    n=(L-2)/2
    k=n*(n+1)/1.5
    def potentials(r):
        f=1-1/r
        odd=f*(L/r**2-3/r**3)
        even=2*f*(n*n*(n+1)*r**3+1.5*n*n*r*r+2.25*n*r+1.125)/(r**3*(n*r+1.5)**2)
        W=k+1.5*f/(r*(n*r+1.5))
        derivative=(((1.5/r**2)*(r*(n*r+1.5))-1.5*f*(2*n*r+1.5))/(r*(n*r+1.5))**2)*f
        return f,odd,even,W,derivative
    def lift(r,v):
        f,odd,even,W,dW=potentials(r)
        return np.array([v[1]+W*v[0], (odd-x*x+dW)*v[0]+W*v[1]])
    r0,r1=1.0003,35.
    odd0=np.array([1.+.4j,-.2+.7j])
    def rhs(r,st):
        f,odd,even,W,dW=potentials(r)
        return np.array([st[1], (odd-x*x)*st[0], st[3], (even-x*x)*st[2]])/f
    sol=solve_ivp(rhs,(r0,r1),np.r_[odd0,lift(r0,odd0)],method="DOP853",rtol=3e-12,atol=2e-13)
    assert sol.success
    s=sol.y[:,-1]
    rel=np.linalg.norm(s[2:]-lift(r1,s[:2]))/np.linalg.norm(s[2:])
    assert rel < 1e-9
    return float(rel)


def primitive_filter():
    # A single loop with survival amplitude r in (0,1); a cut at each return
    # uses a different instrument than reading one output after coherent summation.
    rows=[]
    for m in [2,3,5]:
        r=(m-1)/(m+1)
        for steps in [1,2,4,16]:
            # Port vectors give an inner transfer I + (s_*-1) P on a real line.
            # For the chosen port its dark amplitude (1-s_el)/2 is
            # (1+r)(1+w)/(2m*(1+r*w)), including prompt feed-through.
            b=1/m
            kernel=np.array([b*(1+r)/2]+[b*(1-r*r)*(-r)**(j-1)/2 for j in range(1,steps)])
            gram=np.zeros((steps,steps))
            for i in range(steps):
                gram[i,:i+1]=kernel[i::-1]
            q=np.linalg.norm(gram,ord=2)**2
            assert 0 < q <= b*b+2e-15
            rows.append([m,steps,q])
    return rows


def main():
    time=temporal_results()
    freq=[.25,.5,.7,1.,1.5]
    angular=[angular_image(x) for x in freq]
    for x,row in zip(freq,angular):
        assert abs(row["first_crossing_degrees"]-angular_image(x,7)["first_crossing_degrees"])<4e-5
    checks = [abs(abs(scattering(x,2,70.,12)[0])**2-abs(scattering(x,2)[0])**2) for x in freq]
    assert max(checks)<2e-9
    response=[[x,*polarization(x,2)] for x in freq]
    # At x=0 use the limiting integrand. A Planck-weighted upper bound holds for all ell.
    # Integrate only the quadrupole deficit due to escaping radiation.
    def rate_rule(nodes):
        points,weights=roots_legendre(nodes)
        values=[]
        for x in (points+1)*1.1:
            thermal=1/expm1(4*pi*x)
            values.append(thermal*polarization(float(x),2)[1])
        return 5/(2*pi)*1.1*np.dot(weights,values)
    rate1,rate2=rate_rule(60),rate_rule(86)
    assert abs(rate1-rate2)<3e-11
    # All ell>=2: int x^2/(exp(4*pi*x)-1) dx times 36/Lambda^2.
    from scipy.special import zeta
    constants=36*2*zeta(3)/(2*pi*(4*pi)**3)
    alpha=lambda ell:(ell-1)*ell*(ell+1)*(ell+2)
    bound=constants*sum((2*l+1)/alpha(l)**2 for l in range(2,1001))
    # Exact telescoping sum is 1/108, proved separately.
    assert abs(bound-constants/108)<1e-15
    result=dict(temporal=time,sky=angular,charged=charged_results(),source=primitive_source(),material=material_receipt(),soft=soft_absorption(),matrix=matrix_currents(),quadrupole_parity=response,
                reflected_mark_rate_l2_per_bright_tag=rate2,all_ell_mark_upper=constants/108,
                quadrupole_return_tail_bound=5/(2*pi)*exp(-4*pi*2.2)/(4*pi*(1-exp(-4*pi*2.2))),
                independent_darboux=[darboux_test(.7,2),darboux_test(1.1,3)],
                far_matching_max_abs_difference=max(checks),horizon=horizon_profile(.7),
                primitive_dark=primitive_filter())
    make_figure(result)
    out=ROOT/"verification"/"causal-radiation-results.json"
    out.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf8")
    print("causal-radiation-results.json",time["onset_GammaT"],response,rate2,bound)


def make_figure(result):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig,axes=plt.subplots(1,2,figsize=(8.1,3.15),layout="constrained")
    rows=np.array(result["temporal"]["finite_gate"])
    ax=axes[0]
    ax.loglog(rows[:,0],rows[:,1],"o-",label="Receipt completed by deadline",color="#08776f")
    ax.loglog(rows[:,0],rows[:,2],"s--",label="All later output collected",color="#a3492b")
    ax.set(xlabel=r"Available proper time $\Gamma T$",ylabel="Largest dark-port probability")
    ax.legend(frameon=False,fontsize=7)
    ax=axes[1]
    for x,color in [(.25,"#414e5d"),(.7,"#08776f"),(1.5,"#a3492b")]:
        ells=np.arange(2,9)
        weights=np.array([(2*l+1)*abs(scattering(x,int(l))[0])**2 for l in ells])
        angles=np.linspace(0,pi,161)
        c=np.cos(angles)
        g=sum(w*((1+c)/2)**2*eval_jacobi(l-2,0,4,c) for w,l in zip(weights,ells))/sum(weights)
        ax.plot(angles*180/pi,(1-g*g)/(2*(2+g*g)),color=color,label=fr"$\omega r_s={x}$")
    ax.axhline(1/6,color="#777",ls=":",lw=1)
    ax.set(xlabel="Angle between receiving sites (degrees)",ylabel="Two-receipt mismatch",xlim=(0,180),ylim=(0,.265))
    ax.legend(frameon=False,fontsize=7)
    for ax in axes:
        ax.spines[["top","right"]].set_visible(False)
    fig.savefig(ROOT/"manuscripts"/"causal_radiation_contacts.pdf",metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)


if __name__=="__main__":
    main()
