"""Material clocks, quantum gravitational cascades and retarded transport in Appendix O."""
from fractions import Fraction as F
from itertools import product
import json
import math
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import expm
from scipy.optimize import minimize_scalar
from scipy.special import eval_genlaguerre, roots_legendre
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
QUAD_POINTS, QUAD_WEIGHTS = roots_legendre(6)
UNIT_RULE = tuple(zip((QUAD_POINTS+1)/2, QUAD_WEIGHTS/2))


def material_transform(s, g, width, detuning):
    a = s + width/2
    return 2*width*g*g*a/(s*(s+width)*(a*a+detuning**2)+4*g*g*a*a)


def clock_bounds():
    g, k, detune, nu = .39, .81, .16, .64
    generator = np.array([[0, -1j*g], [-1j*g, -k/2-1j*detune]])
    transform = material_transform(-1j*nu, g, k, detune)
    def density(t): return k*abs(expm(generator*t)[1,0])**2
    integral = complex(quad(lambda t:density(t)*math.cos(nu*t),0,260,epsabs=2e-11)[0],
                       quad(lambda t:density(t)*math.sin(nu*t),0,260,epsabs=2e-11)[0])
    assert abs(integral-transform)<2e-10
    def threshold(k, nu):
        return nu*(k*k+4*nu**2)/(2*(math.hypot(k,nu)+nu))
    cases = []
    for k0, n0 in ((.35,.62),(1.,1.),(3.,.7)):
        a = k0/2-1j*n0
        for d in (0., .33, 1.3):
            b = (-1j*n0)*(k0-1j*n0)*(a*a+d*d)
            c = 4*a*a
            ustar = abs(b)/abs(c)
            exact = abs(b+c*ustar)**2/(4*k0**2*abs(a)**2*ustar)
            opt = minimize_scalar(lambda logu: math.exp(logu)/abs(material_transform(
                -1j*n0,math.exp(logu/2),k0,d))**2, bounds=(-10,10),method="bounded")
            assert abs(opt.fun-exact)<3e-9 and exact>=threshold(k0,n0)-2e-13
            if d==0: assert abs(exact-threshold(k0,n0))<1e-13
            cases.append([k0,n0,d,exact])
    z = material_transform(-1j,math.sqrt(3)/2,2.,0.)
    assert abs(z-.75j)<1e-14
    return {"test_transform":[transform.real,transform.imag],"time_quadrature":[integral.real,integral.imag],
            "threshold_examples":cases,"zero_real_response":[z.real,z.imag]}


def transport():
    # The orbital frame rotates by theta/2. The unitaries are computed without differentiating eigenvectors.
    I = np.eye(2)
    J = np.array([[0.,1.],[-1.,0.]])
    z = material_transform(-1j,math.sqrt(3)/2,2.,0.)
    base = np.diag([.5,-.5])
    def connection(th):
        rot = expm(-th*J/2)
        H = rot @ base @ rot.T
        dH = (H @ J - J @ H)/2
        ev, vec = np.linalg.eigh(H)
        dx = vec.T@dH@vec
        result = np.zeros((2,2),complex)
        for i,j in product(range(2), repeat=2):
            gap = ev[i]-ev[j]
            if i!=j:
                phi = material_transform(-1j*gap,math.sqrt(3)/2,2.,0.)
                result[i,j] = (1-phi)/gap*dx[i,j]
            # The eigenvalues are constant on this loop, so the diagonal derivative vanishes.
        return vec @ result @ vec.T
    def rhs(th,u): return (-connection(th)@u.reshape(2,2)).ravel()
    sol=solve_ivp(rhs,(0,2*math.pi),I.astype(complex).ravel(),method="DOP853",rtol=2e-11,atol=1e-13)
    assert sol.success
    U=sol.y[:,-1].reshape(2,2)
    trace=np.trace(U)/2
    assert abs(trace+math.cos(math.pi*abs(z)))<1e-10 and np.linalg.norm(U.conj().T@U-I)<2e-10
    return {"rabi_clock_modulus":abs(z),"half_trace":trace.real,
            "discard_odd_half_trace":-math.cos(math.pi*z.real),
            "unitarity_error":float(np.linalg.norm(U.conj().T@U-I))}


def radial_polynomial(n,l):
    power=n-l-1
    return {l+j:F((-1)**j*math.comb(n+l,power-j),math.factorial(j))*F(2,n)**(l+j)
            for j in range(power+1)}


def radial_sq(ni,li,nf,lf,order):
    def norm_sq(n,l):
        return F(2,n)**3*F(math.factorial(n-l-1),2*n*math.factorial(n+l))
    total=F(0)
    for i,ai in radial_polynomial(ni,li).items():
        for j,aj in radial_polynomial(nf,lf).items():
            power=2+order+i+j
            total+=ai*aj*math.factorial(power)/(F(1,ni)+F(1,nf))**(power+1)
    exact=norm_sq(ni,li)*norm_sq(nf,lf)*total**2
    def radial(n,l,r):
        v=2*r/n
        return math.sqrt(float(norm_sq(n,l)))*math.exp(-v/2)*v**l*eval_genlaguerre(n-l-1,2*l+1,v)
    independent=quad(lambda r:r**(2+order)*radial(ni,li,r)*radial(nf,lf,r),0,550,
                     epsabs=1e-10,epsrel=2e-12)[0]
    assert math.isclose(independent**2,float(exact),rel_tol=2e-12)
    return exact


def positronium():
    def gap(ni,nf): return (F(1,nf**2)-F(1,ni**2))/2
    def dipole(ni,li,nf,lf,angular):
        return F(4,3)*gap(ni,nf)**3*radial_sq(ni,li,nf,lf,1)*angular
    w4=F(1,4**3)+dipole(4,0,2,1,1)+dipole(4,0,3,1,1)
    w3=dipole(3,2,2,1,F(2,5))
    i43,i31=radial_sq(4,0,3,2,2),radial_sq(3,2,1,0,2)
    g43=F(4,15)*gap(4,3)**5*i43
    g31=F(4,75)*gap(3,1)**5*i31
    return {"radial_squared_in_bohr_units":{"4s3d":str(i43),"3d1s":str(i31)},
            "ordinary_widths_in_mu_alpha5":{"4s":float(w4),"3d":float(w3)},
            "transition_frequencies_in_mu_alpha2":[str(gap(4,3)),str(gap(3,1))],
            "gravity_widths_in_G_mu3_alpha6":[float(g43),float(g31)],
            "gravity_branching_coefficients":[float(g43/w4),float(g31/w3)],
            "both_lines_branching_coefficient":float(g43*g31/(w4*w3)),
            "mean_completion_in_inverse_mu_alpha5":float(1/w4+1/w3)}


def cap_pair(p1,p2):
    # Directions are integrated uniformly over different spherical caps. Azimuth is integrated exactly.
    equal=opposite=0.
    for (x,wx),(y,wy) in product(UNIT_RULE,repeat=2):
        t,w=p1*x,p2*y
        u=t+w-2*t*w
        v2=4*t*(1-t)*w*(1-w)
        def order4(c):return c**4+3*c*c*v2+3*v2*v2/8
        equal+=wx*wy*order4(u)
        opposite+=wx*wy*order4(1-u)
    return 2.5*p1*p2*equal,2.5*p1*p2*opposite


def cap_from_lapse(f, impact=3*math.sqrt(3)):
    # Lengths in black-hole masses. Source inside the photon sphere, falling from rest at infinity.
    radius=2/(1-f)
    mu=math.sqrt(1-impact**2*f/radius**2)
    v=math.sqrt(1-f)
    return impact**2*f**2/(2*radius**2*(1+mu)*(1+v)*(1+v*mu))


def sky():
    full=cap_pair(1.,1.)
    assert np.allclose(full,[.5,.5],atol=2e-14)
    coeff=[F(math.comb(4,k)**2,(k+1)*(5-k)) for k in range(5)]
    narrow=sum(coeff)*F(5,2)
    rare=F(5,2)*sum(v/F(11-2*k) for k,v in enumerate(coeff))
    assert narrow==21
    # Verify helicity amplitudes without prescribing their angular polynomial.
    def tensor(c,s,hand):
        vec=np.array([c,1j*hand,-s])/math.sqrt(2)
        return np.outer(vec,vec)
    for c in np.linspace(-1,1,23):
        for u,v in product((-1,1),repeat=2):
            amp=np.sum(tensor(1.,0.,u)*tensor(c,math.sqrt(1-c*c),v))
            assert abs(abs(amp)**2-((1-u*v*c)/2)**4)<1e-13
    p=1e-7
    for aperture in (.012,.15,.47,.86):
        equal,_=cap_pair(aperture,aperture)
        poly=21+aperture*(-60+aperture*(67.5+aperture*(-35+7*aperture)))
        assert abs(equal-aperture**6*poly)<1e-13
    same,opp=cap_pair(p,p)
    assert abs(same/p**6-21)<1e-5
    assert abs((same+opp)/p**2-2.5)<2e-6
    f=.0001
    h=cap_from_lapse(f)
    assert abs(h/f**2-27/64)<2e-4
    return {"cap_disk_coefficients":[str(x) for x in coeff],"full_sky":list(full),
            "fast_clock_equal_coefficient":str(narrow),"slow_clock_equal_coefficient":str(rare),
            "small_cap_equal_over_p6":same/p**6,"small_cap_both_over_p2":(same+opp)/p**2,
            "independent_equal_over_p2":.5,"example_escape_fraction":h}


def finite_fall():
    # Compare exact varying-radius cone with the near-horizon response for a finite proper-time clock.
    f, xi = .00015, .82
    p=cap_from_lapse(f)
    # Along this geodesic (r/2M)^(3/2) decreases linearly in proper time.
    before=math.expm1(-1.5*math.log1p(-f))
    def inner(t,kind):
        f2=-math.expm1(-2/3*math.log1p((1-t)*before))
        p2=cap_from_lapse(f2)
        eq,opp=cap_pair(p,p2)
        return xi*math.exp(-xi*t)*(eq/p**6 if kind=="same" else (eq+opp)/p**2)
    exact=quad(lambda t:inner(t,"same"),0,1,epsabs=1e-13)[0]
    both=quad(lambda t:inner(t,"both"),0,1,epsabs=1e-13)[0]
    def moment(n):return quad(lambda t:xi*math.exp(-xi*t)*(1-t)**n,0,1)[0]
    leading=2.5*sum(math.comb(4,k)**2/((k+1)*(5-k))*moment(10-2*k) for k in range(5))
    assert abs(exact/leading-1)<.0007 and abs(both/(2.5*moment(2))-1)<.0003
    return {"lapse":f,"remaining_time_in_lifetimes":xi,
            "equal_over_p6":exact,"asymptotic_equal_over_p6":leading,
            "both_over_p2":both,"asymptotic_both_over_p2":2.5*moment(2)}


def polarization_dimensions():
    def tt_matrix(n):
        # Orthogonal projector on all spatial rank-two arrays, with symmetric traceless transverse range.
        d=len(n); P=np.eye(d)-np.outer(n,n)
        tensor=((np.einsum("ik,jl->ijkl",P,P)+np.einsum("il,jk->ijkl",P,P))/2
                -np.einsum("ij,kl->ijkl",P,P)/(d-1))
        return tensor.reshape(d*d,d*d)
    rows={}
    for d in (3,9,10):
        q=d-2; ambient=d*(d+1)//2-1; t=d*(d-1)//2-1
        common=q*(q+1)//2-1
        n=np.eye(d)[0]; first=tt_matrix(n)
        for cosine in (-.83,-.13,.72,1.):
            other=np.array([cosine,math.sqrt(1-cosine**2)]+[0.]*(d-2))
            value=np.einsum("ij,ji",first,tt_matrix(other))
            expected=common+q*cosine**2+((1+q*cosine**2)/(q+1))**2
            assert abs(value-expected)<6e-13
        mean=F(common)+F(q,d)+(1+F(2*q,d)+F(3*q*q,d*(d+2)))/(q+1)**2
        assert mean==F(t*t,ambient)
        rows[str(d+1)]={"physical_tensor_polarizations":t,"parallel_density_enhancement":str(F(ambient,t)),
                        "two_visible_polarizations_given_parallel_pair":str(F(2,t))}
    return rows


def bmn():
    # Evaluate oscillator contractions by explicitly acting on sparse occupation vectors.
    def creation(state, axis, up):
        out={}
        for occ,amp in state.items():
            n=occ[axis]
            if not up and n==0: continue
            oo=list(occ);oo[axis]+=1 if up else -1
            k=tuple(oo);out[k]=out.get(k,0.)+amp*math.sqrt(n+1 if up else n)
        return out
    def pair(state, diagonals, up):
        out={}
        for i,c in enumerate(diagonals):
            if c==0:continue
            for key,amp in creation(creation(state,i,up),i,up).items():out[key]=out.get(key,0.)+c*amp
        return out
    records={}
    for n in (2,3):
        colors=n*n-1; dim=3*colors
        t=np.tile([1/math.sqrt(2),-1/math.sqrt(2),0.],colors)
        vac={(0,)*dim:1.}
        radial=pair(pair(vac,np.ones(dim),True),np.ones(dim),True)
        dstate=pair(vac,t,True)
        norm=lambda v:math.sqrt(sum(abs(a)**2 for a in v.values()))
        s0={key:value/norm(radial) for key,value in radial.items()}
        s1={key:value/norm(dstate) for key,value in dstate.items()}
        v=pair(s0,t,False)
        line1=sum(value*v.get(key,0.) for key,value in s1.items())/2
        line2=pair(s1,t,False)[(0,)*dim]/2
        ratio=(line1/line2)**2
        assert abs(ratio-8/(dim*(dim+2)))<1e-13
        records[str(n)]={"first_residue":line1**2,"second_residue":line2**2,"ratio":ratio}
    return records


def direct_orbital_contact():
    """Compute the local outputs by explicit four-state Kraus evolution."""
    basis = np.eye(4, dtype=complex)
    swap = basis[[0, 2, 1, 3]]
    even = (basis + swap) / 2
    odd = (basis - swap) / 2
    uv, vu = basis[1], basis[2]

    def projector(state):
        return np.outer(state, state.conj())

    def reduced_first(state):
        return np.trace(state.reshape(2, 2, 2, 2), axis1=1, axis2=3)

    rows = []
    for qplus, qminus, angle, residual_overlap in (
        (0., 0., .7, 1.), (.4, .4, math.pi/3, 1.), (1., 1., .4, 1.),
        (.23, .74, -1.2, .67),
    ):
        phase = np.exp(-1j * angle)
        common = math.sqrt(1-qplus)*even + phase*math.sqrt(1-qminus)*residual_overlap*odd
        hidden = phase*math.sqrt((1-qminus)*(1-residual_overlap**2))*odd
        kraus = (common, hidden, math.sqrt(qplus)*even, phase*math.sqrt(qminus)*odd)
        assert np.allclose(sum(k.conj().T@k for k in kraus), basis)

        def channel(vector):
            rho = projector(vector)
            return sum(k@rho@k.conj().T for k in kraus)

        exchange = float(channel(uv)[2, 2].real)
        first = reduced_first(channel((uv+1j*vu)/math.sqrt(2)))
        second = reduced_first(channel((uv-1j*vu)/math.sqrt(2)))
        local_distance = np.linalg.norm(first-second, ord="nuc")/2
        z = np.exp(1j*angle)*math.sqrt((1-qplus)*(1-qminus))*residual_overlap
        assert np.allclose([1-2*exchange,local_distance],[z.real,abs(z.imag)])
        radius_squared = (1-2*exchange)**2 + local_distance**2
        assert radius_squared <= (1-qplus)*(1-qminus)+2e-14
        rows.append({"q_plus":qplus,"q_minus":qminus,"phase":angle,
                     "exchange":exchange,"local_distance":local_distance,
                     "disk_radius_squared":radius_squared})
    return rows


def covariant_line_clock():
    """Two ordinary lines shifted by the direct interaction, with an energy-conserving receiver."""
    half_width = .5  # Energies in the common natural width. Both integrated single-line norms are one.
    amplitude = math.sqrt(half_width/math.pi)

    def local_rates(energy, split, spacing, first_weight=.5):
        def packet(x, shift):
            return amplitude/(x-shift+1j*half_width)
        clock = np.sqrt([first_weight, 1-first_weight])
        plus = clock*np.array([packet(energy, split/2),packet(energy-spacing,split/2)])
        minus = clock*np.array([packet(energy,-split/2),packet(energy-spacing,-split/2)])
        a, b = np.vdot(plus,plus).real, np.vdot(minus,minus).real
        overlap=abs(np.vdot(minus,plus))
        det=abs(plus[0]*minus[1]-plus[1]*minus[0])**2
        denominator = np.prod([abs(x-shift+1j*half_width)**2
                               for x in (energy,energy-spacing) for shift in (split/2,-split/2)])
        analytic = first_weight*(1-first_weight)*amplitude**4*spacing**2*split**2/denominator
        assert math.isclose(det,analytic,rel_tol=2e-7,abs_tol=2e-26)
        # Total success for equal priors. The stable first expression avoids cancellation.
        if overlap <= min(a,b):
            optimal = ((a-b)**2+4*det)/(2*(a+b+2*overlap))
        else:
            optimal = det/(2*min(a,b))
        balanced = 2*det/(a+b+math.hypot(a-b,2*overlap))
        return optimal,balanced

    def success(split, spacing, component):
        # Reflection about spacing/2 exchanges the labels and the two clock levels.
        value=quad(lambda x:local_rates(x,split,spacing)[component],
                   -np.inf,spacing/2,epsabs=1e-15,epsrel=2e-9,limit=120)[0]
        return 2*value

    def ratio(spacing):
        t=math.hypot(1,spacing)
        return (t-1)*(t+2)/t**4

    root=(math.sqrt(73)-3)/4
    best_spacing=math.sqrt(root**2-1)
    search=minimize_scalar(lambda x:-ratio(x),bounds=(.01,5),method="bounded")
    assert abs(search.x-best_spacing)<4e-6
    values=[]
    for split,spacing in ((.65,0.),(.65,.3),(.65,best_spacing),(.65,2.5),
                          (.0002,.42),(.0002,best_spacing),(.0002,2.5)):
        unc=split**2/(math.hypot(1,split)*(math.hypot(1,split)+1))
        optimal=success(split,spacing,0)
        balanced=success(split,spacing,1)
        assert -3e-14<=balanced<=optimal+1e-13 and optimal<=unc+1e-13
        if split<.001:
            assert abs(optimal/unc-ratio(spacing))<8e-5
            assert abs(balanced/unc-ratio(spacing))<1e-6
        values.append({"splitting":split,"clock_gap":spacing,"unrestricted":unc,
                       "covariant_optimum":optimal,"balanced_in_each_energy":balanced})
    # Build the energy-preserving conclusive effects without using the integrated success formula.
    effects_checked = 0
    for e in (-1.8, -.13, .48, 1.04, 2.3):
        for weight in (.25,.5):
            shifts=np.array([.325,-.325])
            clock=np.sqrt([weight,1-weight])[:,None]
            v=clock*amplitude/(np.array([e,e-best_spacing])[:,None]-shifts+1j*half_width)
            gram=v.conj().T@v
            a,b=gram.diagonal().real
            s=abs(gram[0,1])
            if s<=min(a,b):
                accepted=np.array([a-s,b-s])
            elif a>=b:
                accepted=np.array([a-s*s/b,0.])
            else:
                accepted=np.array([0.,b-s*s/a])
            dual=np.linalg.inv(v.conj().T)
            effects=[prob*np.outer(d,d.conj()) for prob,d in zip(accepted,dual.T)]
            assert np.linalg.eigvalsh(np.eye(2)-sum(effects)).min()>-3e-13
            for col,effect in enumerate(effects):
                expected=np.zeros((2,2));expected[col,col]=accepted[col]
                assert np.allclose(v.conj().T@effect@v,expected,atol=2e-13)
            effects_checked+=1
    for spacing in (.42,best_spacing,2.5):
        c=spacing/2; a=half_width; b=math.hypot(a,c)
        def primitive_density(x):
            u=(x+c)**2+a**2;v=(x-c)**2+a**2
            return 1/(u*v*(u+v))
        numeric=quad(primitive_density,-np.inf,np.inf,epsabs=1e-12,epsrel=2e-12)[0]
        assert math.isclose(numeric,math.pi*(2*a+b)/(8*a*b**4*(a+b)),rel_tol=2e-12)
    return {"best_weak_splitting_gap_over_width":best_spacing,
            "best_weak_splitting_fraction":ratio(best_spacing),"cases":values,
            "independently_checked_energy_preserving_effect_pairs":effects_checked}


def plot():
    fig,axes=plt.subplots(1,2,figsize=(8.3,3.05),layout="constrained")
    x=np.linspace(0,3,340)
    phi=material_transform(-1j*x,math.sqrt(3)/2,2.,0.)
    axes[0].plot(x,phi.real,label="Even response",color="#275780")
    axes[0].plot(x,np.abs(phi),label="Full amplitude",color="#a24a25")
    axes[0].axhline(0,color=".6",linewidth=.65)
    axes[0].set(xlabel="Probe gap (clock frequency units)",ylabel="Material response")
    axes[0].legend(frameon=False,fontsize=8)
    p=np.geomspace(.009,.45,130)
    joint=np.array([cap_pair(i,i) for i in p])
    axes[1].loglog(p,joint[:,0]/joint.sum(axis=1),label="Coherent cascade",color="#275780")
    axes[1].loglog(p,np.full_like(p,.5),label="Independent packets",color="#a24a25")
    axes[1].loglog(p,8.4*p**4,"--",color="#407969",label="Narrow cone")
    axes[1].set(xlabel="Fraction of sky accepted",ylabel="Equal helicities given both arrivals")
    axes[1].legend(frameon=False,fontsize=8)
    for ax in axes:ax.grid(alpha=.2)
    pp=ROOT/"manuscripts"/"causal_gravity_receiver.pdf";pp.parent.mkdir(parents=True,exist_ok=True)
    fig.savefig(pp,metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)


if __name__=="__main__":
    result={"clock":clock_bounds(),"transport":transport(),"atom":positronium(),"sky":sky(),
            "finite_fall":finite_fall(),"tensor_channels":polarization_dimensions(),"matrix":bmn(),
            "direct_contact":direct_orbital_contact(),"covariant_line_clock":covariant_line_clock()}
    dest=ROOT/"verification"/"causal-gravity-receiver-results.json"
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf-8")
    plot()
    print(json.dumps(result,indent=2))
