"""Transfer from a falling odd mass multipole to radiation and to relational ports."""
import json
from math import comb, exp, factorial, pi, sqrt
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import expm, svdvals
from scipy.optimize import brentq
from scipy.special import eval_genlaguerre, eval_legendre, i0e, roots_legendre

ROOT = Path(__file__).resolve().parents[1]


def expectation(func, lo=-1., hi=1.):
    return quad(func, lo, hi, epsabs=2e-13, epsrel=3e-12)[0]


def angular_weight(m, u):
    t = (1+u)/2
    return 5*comb(4, 2+m)/4*(t**(2+m)*(1-t)**(2-m) + t**(2-m)*(1-t)**(2+m))


def cone_width(r):
    # Rationalized 1-cos(theta) in the falling frame, r in Schwarzschild radii.
    v = 1/sqrt(r)
    sine2 = 27*(r-1)/(4*r**3)
    mu_static = (1.5-r)*sqrt((r+3)/r**3)
    one_minus_static = sine2/(1+mu_static) if r<=1.5 else 1-mu_static
    return ((r-1)/(r*(1+v)))*one_minus_static/(1+v*mu_static)


def radiative_kernel(h, visibility, tag):
    return expectation(lambda u: angular_weight(2,u)*(1-tag*visibility*np.cos(h*u)))


def fall_readout(r0, r1, width_rs, loss_ratio, h, visibility, tag):
    total = width_rs*(radiative_kernel(h,visibility,tag)+loss_ratio)
    def density(r):
        delta = cone_width(r)
        def accepted(t):
            u = 1-delta*t
            return 5/4*u*u*(1-tag*visibility*np.cos(h*u))
        proper = (2/3)*(r0**1.5-r**1.5)
        return width_rs*sqrt(r)*exp(-total*proper)*delta*expectation(accepted,0,1)
    return expectation(density,r1,r0)


def angular_results():
    for m in (0,1,2):
        assert abs(expectation(lambda u:angular_weight(m,u))-1)<2e-14
    assert abs(expectation(lambda u:u*u*angular_weight(2,u))-11/21)<2e-15
    for u in (-.9,-.4,.2,.9):
        t = (1+u)/2
        pol = np.array([[t*t,(1-t)**2],[(1-t)**2,t*t]])
        assert abs(min(svdvals(pol))**2-u**2)<2e-15
    ds = [cone_width(1+x) for x in (.03,.01,.003,.001)]
    assert abs(ds[-1]/.001**2-27/32)<.002
    # The cap can be narrower than the precision of rounding cos(theta) itself.
    caps=[]
    for e in (.5,.2,.1,.03,.01,.003):
        d=cone_width(1+e)
        five=d*expectation(lambda t:15/16*(d*t*(2-d*t))**2,0,1)
        spin=d*5/4*(1-d+d*d/3)
        caps.append([e,d,spin,five])
    h=.2
    thin=radiative_kernel(h,1.,1.)
    fourth = expectation(lambda u:u**4*angular_weight(2,u))
    assert 0 <= 11*h*h/42-thin <= h**4*fourth/24
    return dict(cap=caps, residual_dark_width_at_kL_point2=thin)


def radial(n, l, r):
    norm=(2/n)**1.5*sqrt(factorial(n-l-1)/(2*n*factorial(n+l)))
    return norm*(2*r/n)**l*np.exp(-r/n)*eval_genlaguerre(n-l-1,2*l+1,2*r/n)


def moment(upper,l,lower,j,order):
    return expectation(lambda r:r**(2+order)*radial(upper,l,r)*radial(lower,j,r),0,np.inf)


def line(l,lower,j):
    angular=expectation(lambda u:eval_legendre(l,u)*eval_legendre(2,u)*eval_legendre(j,u))*(2*j+1)/3
    w=(1/lower**2-1/16)/2
    return (2/5)*w**5*angular*moment(4,l,lower,j,2)**2


def material():
    q=sqrt(2/15)*moment(4,2,1,0,2)
    o=sqrt(6/35)*moment(4,3,1,0,3)
    target=line(2,1,0)
    d_widths=[line(2,n,j) for n,j in ((1,0),(2,0),(3,0),(3,2))]
    f_widths=[line(3,n,1) for n in (2,3)]
    assert abs(target-(2/5)*(15/32)**5*q*q)<3e-18
    assert abs(moment(4,2,4,2,2)-504)<3e-11
    assert abs(moment(4,3,4,3,2)-360)<3e-11
    # The crossover of gravitational-atom fine structure and the diagonal tides.
    # A positive test of the root in this truncation does not bound higher shifts by the linewidth.
    alpha=1e-6
    separation=brentq(lambda A:-3*alpha*alpha/560+15*alpha*alpha/(64*A)+162/A**3,100,1e7)
    nu=.01
    asymmetry=sqrt(1-4*nu)
    phase = sqrt(5)*2656/315*nu*asymmetry*abs(o*q)*separation**(-4.5)
    direct_integral=expectation(lambda s: 2*(1+s*s)**4,0,1)
    assert abs(direct_integral-2656/315)<1e-13
    vals=[]
    for gap in (40.,100.,500.,separation):
        vals.append([gap,sqrt(5)*direct_integral*nu*asymmetry*abs(o*q)*gap**(-4.5)])
    return dict(quadrupole=q,octupole_without_mass_asymmetry=o,
                quadrupole_widths_d=d_widths,quadrupole_widths_f=f_widths,
                loss_to_ground_ratio=sum(d_widths[1:])/target,donor_loss_to_target=sum(f_widths)/target,
                candidate_resonance_A=separation,kL_at_crossing=(15/16)*alpha*separation,
                max_population_first_half=phase**2,phase_bounds=vals)


def coupled_source(gap, loss_d, loss_f, branch_tag, omega, duration):
    width_arm=radiative_kernel(.2, .999, branch_tag)
    gen=np.array([[-loss_f/2,-1j*omega],[-1j*omega,-(loss_d+width_arm)/2-1j*gap]])
    def pop(t):
        a,b=expm(gen*t)[:,0]
        return abs(b)**2
    emitted=expectation(pop,0,duration)*width_arm
    def evolution(t,y):
        a,b,j,l=y
        da,db=gen@np.array([a,b])
        return [da,db,width_arm*abs(b)**2,loss_f*abs(a)**2+loss_d*abs(b)**2]
    sol=solve_ivp(evolution,(0,duration),np.array([1.,0.,0.,0.],complex),
                  rtol=1e-10,atol=2e-13,method="DOP853")
    a,b,j,l=sol.y[:,-1]
    assert abs(emitted-j)<3e-10 and abs(abs(a)**2+abs(b)**2+j+l-1)<1e-9
    return [float(emitted),float(abs(a)**2+abs(b)**2),float(l.real)]


def vertex(k):
    n=k+2
    return np.full((n,n),2/n)-np.eye(n)


def graph():
    data={}
    for k in (1,2,3,6):
        s=vertex(k)
        assert np.allclose(s.T@s,np.eye(k+2))
        odd=np.array([1,-1])/sqrt(2)
        rho=np.outer(odd,odd)
        rows=[]
        for z in (0.,.3,.8,1.):
            rest=rho.copy()
            bright=np.array([0.,1.])
            mix=np.array([[1+z,1-z],[1-z,1+z]])/2
            transfer=np.diag([((2-k)/(2+k))**2,1.])@mix
            trace=[]
            for step in range(1,13):
                cut=z*rest+(1-z)*np.diag(np.diag(rest))
                rest=s[:2,:2]@cut@s[:2,:2].T
                bright=transfer@bright
                assert abs(np.trace(rest)-sum(bright))<2e-14
                if k==2: assert abs(sum(bright)-((1+z)/2)**step)<2e-14
                if step in (1,4,12):trace.append(float(sum(bright)))
            rows.append([z,*trace])
        data[str(k)]=rows
    # Return probabilities for two valence-eight infinite homogeneous networks.
    def heat2(t,order):
        x,w=roots_legendre(order)
        c=np.cos((x+1)*pi/2)
        lam=1-(c[:,None]+c[None,:]+2*c[:,None]*c[None,:])/4
        return float(w@np.exp(-t*lam)@w/4)
    diffusion=[]
    for t in (4.,16.,64.,256.):
        k2=heat2(t,112)
        assert abs(k2-heat2(t,152))<1e-14
        k4=float(i0e(t/4)**4)
        diffusion.append([t,k2,k4,t*k2,t*t*k4])
    return dict(return_survival=data, diffusion=diffusion,
                limits=[2/(3*pi),4/pi**2])


def string_and_matrix():
    # Swapping two indistinguishable cycles is gauge; unequal lengths are physical addresses.
    # Coherent reduction uses an explicit output spin and records which keep no spin label.
    I=np.eye(2)
    legs=[np.kron(b.reshape(1,2),I) for b in np.eye(2)]
    antisym=np.kron(np.array([[1.],[-1.]])/sqrt(2),I)
    maps=[leg@antisym for leg in legs]
    assert np.linalg.norm(sum(maps))<2e-15
    bell=np.eye(2).ravel()/sqrt(2)
    pair=np.outer(bell,bell)
    out=sum(np.kron(I,m)@pair@np.kron(I,m).T for m in maps)
    assert np.max(abs(out-pair))<4e-15
    # No trace-labelled blocks. Opposite velocities and axial separation are physical.
    X=np.diag([-1.,1.])
    Q=np.diag([.7,-.7])
    P=[(I-X)/2,(I+X)/2]
    rot=np.array([[3.,-4.],[4.,3.]])/5
    assert abs(np.trace(Q))<1e-14
    separate=sum(abs(np.trace(p@Q))**2 for p in P)
    assert abs(separate-sum(abs(np.trace((rot@p@rot.T)@(rot@Q@rot.T)))**2 for p in P))<1e-14
    return dict(string_bell_fidelity=float(bell@out@bell),
                matrix_coherent=abs(float(np.trace(Q)))**2,matrix_resolved=float(separate))


def thermal_receipt():
    """Trace the inaccessible partner and count exactly one transmitted polarization quantum."""
    def evaluate(s,eta,angle,nmax):
        # Each |ground;n+1,N-n> has one bright excited combination at fixed total energy.
        p_one=spin_one=p_ground=spin_ground=0.
        for N in range(nmax+1):
            den=N+1
            c=np.cos(angle*sqrt(den))
            sine=np.sin(angle*sqrt(den))
            weight=(1-s)**2*s**N
            exit_g=den*eta*(1-eta)**N
            exit_e=N*eta*(1-eta)**(N-1) if N else 0.
            for n in range(N+1):
                g=(n+1)*sine*sine/den
                same=(1+(c-1)*(n+1)/den)**2
                exchange=(c-1)**2*(n+1)*(N-n)/den**2
                assert abs(g+same+exchange-1)<2e-14
                pg=weight*g*exit_g
                sg=pg*(2*(n+1)-den)/den
                p_ground+=pg
                spin_ground+=sg
                p_one+=pg+weight*exit_e*(same+exchange)
                spin_one+=sg+weight*exit_e*(same*(2*n-N)+exchange*(2*n+2-N))/max(1,N)
        return np.array([p_one,spin_one/p_one,p_ground,spin_ground/p_ground])
    rows=[]
    for s,eta in ((.35,.28),(.12,.65)):
        t=s*(1-eta)
        shrink=1/(1+2*t)
        p1=eta*(1-s)**3*(1+2*t)/(1-t)**4
        check=evaluate(s,eta,1e-4,64)
        assert abs(check[3]-shrink)<2e-8
        assert abs(check[2]/(1e-8/(1-s))-p1)<2e-8
        for angle in (.15,.7,1.4):
            vals=evaluate(s,eta,angle,64)
            assert np.max(abs(vals-evaluate(s,eta,angle,80)))<3e-13
            rows.append([s,eta,angle,*vals.tolist(),max(0.,(3*vals[1]-1)/4)])
    return rows


def main():
    a=angular_results()
    m=material()
    intensity=[]
    for gamma in (.1,1.,4.):
        thin=fall_readout(1.5,1.02,gamma,m["loss_to_ground_ratio"],.2,.999,1.)
        marked=fall_readout(1.5,1.02,gamma,m["loss_to_ground_ratio"],.2,.999,0.)
        intensity.append([gamma,thin,marked,.75*thin+.25*marked])
    conditional=[coupled_source(0.,m["loss_to_ground_ratio"],m["donor_loss_to_target"],z,
                                2*sqrt((1+z)/2),2.) for z in (1.,0.)]
    mass_fraction=1.338183/(1.338183+1.248869)
    pulsar_loss=(1-.999963+1.96*.000063)/(2*mass_fraction*(1-mass_fraction))
    for z in (0.,.25,.6,1.):
        c=sqrt((1+z)/2)
        gram=np.array([[1,c,c],[c,1,z],[c,z,1]])
        assert min(np.linalg.eigvalsh(gram))>-8e-15
    max_strength=[]
    for u in (.2,.5,.9,.999):
        opt=min(1.,(1-u)/(2*u))
        predicted=(1+opt)*(1-u*opt)/2
        grid=np.linspace(0.,1.,10001)
        assert abs(predicted-np.max((1+grid)*(1-u*grid)/2))<4e-9
        max_strength.append([u,opt,predicted])
    result=dict(angular=a, material=m, falling_unknown_qubit=intensity,
                supported_resonant_example=conditional, pulsar_conditional_95=pulsar_loss,
                tag_tradeoff=max_strength, thermal_receipts=thermal_receipt(), relational=graph(),microscopic=string_and_matrix())
    file=ROOT/"verification"/"falling-multipoles-results.json"
    file.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf8")
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig,axes=plt.subplots(1,2,figsize=(8,3.1),layout="constrained")
    eps=np.geomspace(.015,.5,85)
    width=np.array([cone_width(1+e) for e in eps])
    axes[0].loglog(eps,5/4*width*(1-width+width**2/3),color="#146c72",label="Two spin states, recoil traced")
    axes[0].loglog(eps,15/16*width**3*(4/3-width+width**2/5),color="#984b32",label="All five, coherent aperture")
    axes[0].set(xlabel=r"Height above horizon $(r-r_s)/r_s$",ylabel="Recoverable fraction per emission")
    axes[0].legend(fontsize=7,frameon=False)
    n=np.arange(0,13)
    for z,color in [(1,"#323b4c"),(.8,"#984b32"),(0,"#146c72")]:
        axes[1].plot(n,((1+z)/2)**n,"o-",ms=2.5,color=color,label=fr"Address overlap $z={z}$")
    axes[1].set(xlabel="Physical returns to the same junction",ylabel="Probability excitation remains",ylim=(-.03,1.06))
    axes[1].legend(fontsize=7,frameon=False)
    for ax in axes: ax.spines[["top","right"]].set_visible(False)
    fig.savefig(ROOT/"manuscripts"/"falling_multipoles.pdf",metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)
    print(file.name,intensity,conditional)


if __name__=="__main__":
    main()
