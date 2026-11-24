"""Physical matrix fluctuations in a shrinking sphere and a Schwarzschild tidal tube."""
import json
from pathlib import Path

import numpy as np
from scipy import linalg
from scipy.integrate import solve_ivp, quad

from cat_singular_clock import matrix_background

ROOT = Path(__file__).resolve().parents[1]


def spin_matrices(ell):
    magnetic = np.arange(-ell,ell+1,dtype=float)
    raising = np.diag(np.sqrt((ell-magnetic[:-1])*(ell+magnetic[:-1]+1)), -1)
    return [(raising+raising.T)/2, (raising-raising.T)/(2j), np.diag(magnetic)]


def harmonic_spectra(ell):
    # Compare the actual linearized force to total-spin addition.
    L = spin_matrices(ell)
    n = 2*ell+1
    div = np.hstack(L)
    identity = np.eye(n)
    svec = []
    for m in range(3):
        s = np.zeros((3,3),complex)
        s[(m+1)%3,(m+2)%3] = -1j
        s[(m+2)%3,(m+1)%3] = 1j
        svec.append(s)
    spin_orbit = sum(np.kron(s,l) for s,l in zip(svec,L))
    hessian = ell*(ell+1)*np.eye(3*n)-2*spin_orbit-div.conj().T@div
    basis = linalg.null_space(div)
    vals = np.linalg.eigvalsh(basis.conj().T@hessian@basis)
    expect = [ell*(ell-1)]*(2*ell+3)+[(ell+1)*(ell+2)]*(2*ell-1)
    np.testing.assert_allclose(vals,sorted(expect),atol=5e-12)
    # The gauge direction proportional to a(T) solves the background equation.
    np.testing.assert_allclose(hessian@div.conj().T,2*div.conj().T,atol=1e-11)
    pauli = [np.array([[0,1],[1,0]]),np.array([[0,-1j],[1j,0]]),np.diag([1,-1])]
    dirac = sum(np.kron(s,l) for s,l in zip(pauli,L))
    fvals = np.linalg.eigvalsh(dirac)
    np.testing.assert_allclose(fvals,[-ell-1]*(2*ell)+[ell]*(2*ell+2),atol=2e-13)
    # Construct the linearized double commutator by a second route in index order.
    raw = np.block([[ (ell*(ell+1)*identity if i==j else np.zeros((n,n)))
                       -L[j]@L[i]+L[i]@L[j]-L[j]@L[i]
                      for j in range(3)] for i in range(3)])
    np.testing.assert_allclose(hessian,raw,atol=4e-13)
    return dict(ell=ell,transverse_triplet=basis.shape[1],gauge=n,
                positive_majorana=8*n,vector_eigen_error=float(max(abs(vals-sorted(expect)))))


def field_content(j):
    # Frequencies and degeneracies of the physical, nonconstant bosons.
    ell = np.arange(1,2*j+1,dtype=float)
    masses = np.concatenate((ell*(ell+1),ell*(ell-1),(ell+1)*(ell+2)))
    multiplicity = np.concatenate((6*(2*ell+1),2*ell+3,2*ell-1))
    unique = np.unique(masses)
    counts = np.array([np.sum(multiplicity[masses==l]) for l in unique])
    assert counts[0]==5 and sum(counts)==8*((2*j+1)**2-1)
    inertia=(2*j+1)*j*(j+1)
    fermion_vacuum_slope=8*np.sum(ell*(ell+1))
    np.testing.assert_allclose(fermion_vacuum_slope/inertia,32/3)
    return unique[1:],counts[1:],inertia,fermion_vacuum_slope


def spherical_force(j,g2):
    lam,deg,I,F=field_content(j)
    initial_radius,initial_velocity=.6,-.8
    w0=initial_radius*np.sqrt(lam)
    mode_count=len(lam)
    initial=np.r_[initial_radius,initial_velocity,1/np.sqrt(2*w0),np.zeros(mode_count),
                  np.zeros(mode_count),-np.sqrt(w0/2)]
    def unpack(v):
        return v[0],v[1],*v[2:].reshape(4,-1)
    def rhs(t,v):
        a,vel,re,im,dre,dim=unpack(v)
        bforce=np.sum(deg*lam*(re*re+im*im))
        return np.r_[vel,-2*a**3+g2*(F-a*bforce)/I,dre,dim,-a*a*lam*re,-a*a*lam*im]
    def turn(t,v):
        return v[1]
    def zero(t,v):
        return v[0]
    turn.terminal=True
    turn.direction=1
    zero.direction=-1
    sol=solve_ivp(rhs,(0,6),initial,method="DOP853",dense_output=True,events=(turn,zero),
                  rtol=5e-12,atol=8e-14)
    assert sol.success and len(sol.t_events[0])==1
    final=sol.t_events[0][0]
    energies=[]
    wronskians=[]
    for t in np.linspace(0,final,61):
        a,vel,re,im,dre,dim=unpack(sol.sol(t))
        bose=.5*np.dot(deg,dre**2+dim**2+lam*a*a*(re**2+im**2))
        # Geometry energy per inertia, with the ordinary g_1^2 absorbed.
        energies.append(.5*(vel**2+a**4)+g2*(bose-F*a)/I)
        wronskians.append(max(abs(re*dim-im*dre+.5)))
    error=max(abs(np.array(energies)-energies[0]))
    assert error<1e-8 and max(wronskians)<1e-8
    amin=sol.y_events[0][0,0]
    # Energy cost for a vacuum at +a0 to arrive at -a0 with any terminal speed.
    threshold=3*initial_velocity**2/(128*initial_radius)
    if g2>threshold:
        assert amin>-initial_radius
    return dict(j=j,g2=g2,initial_energy=energies[0],first_zero=(
        sol.t_events[1][0] if len(sol.t_events[1]) else None),first_turn=final,
        signed_radius_at_turn=amin,fermion_work_equal_radius_per_inertia=2*F*initial_radius/I,
        fermion_only_necessary_g2=threshold,energy_drift=error,
        wronskian_error=max(wronskians))


def quantum_reach(j,g2,sigma=.04):
    # Quantize the signed collective radius once. Its J=0 oscillator belongs
    # to that coordinate and is removed from the independent angular tower.
    lam,deg,I,F=field_content(j)
    deg=deg.copy()
    deg[lam==6]-=1
    B=.5*np.dot(deg,np.sqrt(lam))
    mu=I/g2
    a0,v0=.6,-.8
    anchor=((F-B)/(2*mu))**(1/3)
    floor=-1.5*mu*anchor**4
    energy=(mu*v0*v0/2+1/(8*mu*sigma**2)+mu*(a0**4+6*a0*a0*sigma**2+3*sigma**4)/2
            +B*(a0+sigma**2/(2*a0))-F*a0)
    cost=mu*a0**4/2+(B+F)*a0
    upper=min(1.,(energy-floor)/(cost-floor))
    assert 0<upper<=1. and 2*j<=F-B<=6*j+np.sqrt(6)/2+1e-11
    return dict(j=j,g2=g2,initial_radius_sigma=sigma,energy_per_inertia=energy/I,
                energy_floor_per_inertia=floor/I,deficit_per_inertia=(F-B)/I,
                negative_slope_per_inertia=(B+F)/I,far_side_probability_bound=upper)


def circular_fermions(ell):
    # Work in one complex eight-dimensional Cl(6) module, then double for
    # the sixteen-component adjoint Majorana spinor of the clock theory.
    px=np.array([[0,1],[1,0]])
    py=np.array([[0,-1j],[1j,0]])
    pz=np.diag([1,-1])
    ident2=np.eye(2)
    gamma=[]
    for i in range(3):
        for pauli in (px,py):
            factors=[pz]*i+[pauli]+[ident2]*(2-i)
            gamma.append(np.kron(np.kron(factors[0],factors[1]),factors[2]))
    n=2*ell+1
    D=sum(np.kron(g,L) for g,L in zip(gamma[:3],spin_matrices(ell)))
    G=sum(gamma[i+3]@gamma[i] for i in range(3))/2
    omega=np.sqrt(2.)
    K=np.kron(-1j*omega*G,np.eye(n))
    en,vec=np.linalg.eigh(D)
    positive=en>0
    initial_frame=vec[:,~positive]
    H=D+K
    energies,modes=np.linalg.eigh(H)
    moved=modes@(np.exp(-1j*energies*np.pi/omega)[:,None]*(modes.conj().T@initial_frame))
    prob=np.sum(abs(vec[:,positive].conj().T@moved)**2,axis=1)
    excitation=2*np.dot(en[positive],prob)
    trace_shift=np.trace(moved.conj().T@D@moved-initial_frame.conj().T@D@initial_frame).real
    np.testing.assert_allclose(trace_shift,excitation,rtol=1e-10,atol=2e-10)
    upper=12*(2*ell+1)/ell
    assert excitation<=upper+2e-11
    return dict(ell=ell,straight_energy=16*ell*(ell+1),circular_energy=float(excitation),
                circular_exact_upper=upper,ratio=float(excitation/(16*ell*(ell+1))))


def sphere_results():
    return dict(harmonic_checks=[harmonic_spectra(l) for l in (1,2,3,5)],
                circular_fermions=[circular_fermions(l) for l in (1,2,4,8,16)],
                quantum_energy_bounds=[quantum_reach(j,g) for j,g in ((8,.01),(8,.03),(8,.1),(8,1.),(16,1.),(32,1.),(128,1.))],
                backreaction=[spherical_force(j,g) for j,g in ((8,0.),(8,.01),(8,.03),
                              (8,.1),(8,1.),(16,.03),(32,.03))])

def bump_derivatives(z):
    if abs(z)>=1:
        return 0.,0.
    inv=1/(1-z*z)
    value=np.exp(1-inv)
    return (-2*z*inv**2*value,
            value*(4*z*z*inv**4-2*inv**2-8*z*z*inv**3))


def matched_caps():
    """Same incoming/outgoing matrices and affine readings, changed only inside."""
    clock,base,end,_=matrix_background(0.)
    left,right=clock(-.75),clock(.75)
    middle,width=(left+right)/2,(right-left)/2
    def coefficients(u,strength):
        a,b,f=base(u)
        fp=np.hypot(a,b)/np.sqrt(1+f*f)
        if strength==0 or not left<u<right:
            return a,b,f,fp
        first,second=bump_derivatives((u-middle)/width)
        f_new=np.sqrt(f*f+strength*first)
        deriv=(2*f*fp+strength*second/width)/(2*f_new)
        scale=(deriv/fp)*np.sqrt((1+f_new*f_new)/(1+f*f))
        return a*scale,b*scale,f_new,deriv
    return clock,coefficients,(left,right),end


def spin_generators():
    x=np.array([[0,1],[1,0]])
    y=np.array([[0,-1j],[1j,0]])
    z=np.diag([1,-1])
    # Spin(4) Dirac doubled is the restriction of physical chiral Spin(8).
    return [np.kron(x,np.eye(2)),np.kron(y,np.eye(2)),np.kron(z,x),np.kron(z,y)]


def check_yukawa_and_material(fp,fm,k):
    # Interior oscillator states realize [q,p]=i; the regulator's top mode is excluded.
    size=7
    lowering=np.diag(np.sqrt(np.arange(1,size)),1)
    q=(lowering+lowering.T)/np.sqrt(2)
    mom=(lowering-lowering.T)/(1j*np.sqrt(2))
    ident=np.eye(size)
    ql,qr=np.kron(q,ident),np.kron(ident,q)
    pl,pr=np.kron(mom,ident),np.kron(ident,mom)
    D=[ql-qr,pl+pr,fp*ql-fm*qr,fp*pl+fm*pr]
    gamma=spin_generators()
    ket=np.zeros((4,size,size),dtype=complex)
    ket[0,2,3],ket[3,1,2]=.6,.8j
    ket=ket.ravel()
    dirac=sum(np.kron(g,d) for g,d in zip(gamma,D))
    blocks=np.array([[0.,fp-fm],[fp-fm,fp**2-fm**2]])
    dc=np.kron(blocks,np.array([[0.,1.],[-1.,0.]]))
    spin=1j*sum(dc[i,j]*(gamma[i]@gamma[j]) for i in range(4) for j in range(i+1,4))
    orbital=sum(d@d for d in D)
    square_error=np.linalg.norm(dirac@(dirac@ket)-np.kron(np.eye(4),orbital)@ket
                                -np.kron(spin,np.eye(size**2))@ket)
    b=np.zeros((size,size),dtype=complex)
    b[1,2]=1
    xp,xm=fp*mom,fm*mom
    av=-(xp@b-b@xm)/k
    bq=b@q-q@b
    # Differentiate the original scalar double commutators and impose Gauss.
    source=(k*(av@q-q@av)+b@(xm@q-q@xm)-(xp@q-q@xp)@b+xp@bq-bq@xm)
    material_error=np.linalg.norm(source-2j*(fp-fm)*b)
    assert square_error<5e-13 and material_error<5e-13
    return dict(dirac_square_error=float(square_error),material_source_error=float(material_error))


def polarized_transfer(clock,coefficients,strength,k,direct=False):
    start,stop=clock(-1.4),clock(1.4)
    gamma=spin_generators()
    c=np.sqrt(.5)
    generator2=np.array([[0.,1.],[-1.,0.]])
    def derivatives(u,v):
        if k==0:  # Smooth nonzero-k limit. The constrained k=0 sector is separate.
            _,_,f,slope=coefficients(u,strength)
            square_slope=2*f*slope
        else:
            plus=coefficients(u+k/2,strength)[2]
            minus=coefficients(u-k/2,strength)[2]
            slope=(plus-minus)/k
            square_slope=(plus+minus)*slope
        generator=np.kron(np.array([[0.,slope],[slope,square_slope]]),generator2)
        if direct:
            three=np.array([[0.,c*slope,0.],[c*slope,square_slope,c*slope],[0.,c*slope,0.]])
            return (np.kron(three,generator2)@v.reshape(6,6)).ravel()
        spin=.5*sum(generator[i,j]*(gamma[i]@gamma[j]) for i,j in ((0,3),(1,2),(2,3)))
        R,S=v[:16].reshape(4,4),v[16:].reshape(4,4)
        return np.r_[(generator@R).ravel(),(spin@S).ravel()]
    initial=np.eye(6).ravel() if direct else np.tile(np.eye(4,dtype=complex).ravel(),2)
    sol=solve_ivp(derivatives,(start,stop),initial,method="DOP853",
                  rtol=6e-12,atol=2e-14,max_step=.016)
    assert sol.success
    v=sol.y[:,-1]
    if direct:
        return v.reshape(6,6)
    R,S=v[:16].real.reshape(4,4),v[16:].reshape(4,4)
    np.testing.assert_allclose(R.T@R,np.eye(4),atol=4e-11)
    np.testing.assert_allclose(S.conj().T@S,np.eye(4),atol=4e-11)
    for j in range(4):
        np.testing.assert_allclose(S@gamma[j]@S.conj().T,sum(R[i,j]*gamma[i] for i in range(4)),
                                   atol=7e-11)
    return R,S


def null_results():
    clock,coefficients,(left,right),end=matched_caps()
    eta=.08
    f=lambda u,d: coefficients(u,d)[2]
    clock_difference=quad(lambda u:f(u,eta)**2-f(u,0.)**2,left,right,
                          epsabs=2e-14,epsrel=5e-13)[0]
    np.testing.assert_allclose(clock_difference,0.,atol=3e-13)
    for u in np.r_[np.linspace(.2,left,9),np.linspace(right,end,9)]:
        np.testing.assert_array_equal(coefficients(u,0.),coefficients(u,eta))
    ricci=[]
    for u in np.linspace(left+.002,right-.002,61):
        a,b,fd,_=coefficients(u,eta)
        h=1e-5
        d=(f(u-2*h,eta)-8*f(u-h,eta)+8*f(u+h,eta)-f(u+2*h,eta))/(12*h)
        ricci.append(abs(a*a+b*b-(1+fd*fd)*d*d))
    assert max(ricci)<3e-7
    rows=[]
    for k in (0.,.00125,.0025,.005,.01,.02,.04,.08,.16):
        assert clock(-1.4)-k/2>0 and clock(1.4)+k/2<end
        pair=[polarized_transfer(clock,coefficients,h,k) for h in (0.,eta)]
        R0,S0=pair[0]
        R1,S1=pair[1]
        material=[]
        for R in (R0,R1):
            amp=.5*(R-np.eye(4))[:2,0]
            material.append(float(amp@amp))
        if k in (0.,.08):
            for strength,prob in zip((0.,eta),material):
                extended=polarized_transfer(clock,coefficients,strength,k,direct=True)
                np.testing.assert_allclose(np.sum(extended[4:6,0]**2),prob,atol=3e-11)
        row=dict(k=k,vector_frobenius=float(np.linalg.norm(R1-R0)),
                 spinor_frobenius_per_copy=float(np.linalg.norm(S1-S0)),
                 material_probabilities=material)
        if k>=.04:
            # All eight vector eigenvalues include four fixed spectator ones.
            eigenvalues=np.linalg.eigvals(R0.T@R1)
            theta=max(abs(np.angle(eigenvalues)))
            copies=int(np.ceil(np.pi/(2*theta)))
            assert (copies-1)*theta<np.pi/2<=copies*theta<np.pi
            assert abs(material[0]-material[1])<=np.sin(theta)
            row.update(max_relative_angle=float(theta),best_single_success=float((1+np.sin(theta))/2),
                       ideal_parallel_uses_for_orthogonality=copies)
        rows.append(row)
    assert rows[0]["vector_frobenius"]<2e-10
    slopes=[np.log2(rows[i+1]["vector_frobenius"]/rows[i]["vector_frobenius"]) for i in (1,2)]
    assert all(1.97<s<2.03 for s in slopes)
    middle=(left+right)/2
    direct=check_yukawa_and_material(f(middle+.04,eta),f(middle-.04,eta),.08)
    return dict(deformation=eta,affine_shift=clock_difference,finite_difference_ricci=max(ricci),
                direct_matrix_checks=direct,
                near_zero_exponents=slopes,reads=rows)


def main():
    result=dict(sphere=sphere_results(),null_tube=null_results())
    dest=ROOT/"verification/cat-core-multiplet-results.json"
    dest.write_text(json.dumps(result,ensure_ascii=False,allow_nan=False,indent=2)+"\n",encoding="utf8")
    print("Checked physical boson and fermion spectra, backreaction, spin transport and material response.")


if __name__=="__main__":
    main()
