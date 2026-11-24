"""Relational propagation near a degenerate metric and a Schwarzschild null tide."""
import json
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
from scipy import sparse, special
from scipy.sparse.linalg import eigsh, expm_multiply

ROOT = Path(__file__).resolve().parents[1]
J2 = np.array([[0., -1.], [1., 0.]])
J4 = np.block([[np.zeros((2,2)), np.eye(2)], [-np.eye(2), np.zeros((2,2))]])


def tidal_profile(affine, deformation):
    """The two trace-free profiles agree exactly on both exterior intervals."""
    x2 = affine*affine
    bump = np.exp(1-1/(1-x2)) if x2<1 else 0.
    return (6/25)*(1+deformation*bump)/(x2+bump)


def matrix_background(deformation):
    # Integrate in the spectral reading u of the canonically conjugate pair.
    # The emergent affine parameter is the first returned component.
    def rhs(u, state):
        t, mx, my, f = state
        s = 1+f*f
        v = tidal_profile(t,deformation)*np.array([np.cos(f*f),-np.sin(f*f)])
        mprime = -s*(s*np.eye(2)-J2)@v/(s*s+1)
        return [s,*mprime,np.hypot(mx,my)*np.sqrt(s)]
    def finish(u, state):
        return state[0]-2
    finish.terminal = True
    finish.direction = 1
    sol = solve_ivp(rhs,(0.,4.),[-2.,0.,.8,0.],events=finish,method="DOP853",
                    dense_output=True,rtol=4e-12,atol=2e-14,max_step=.025)
    assert sol.success and len(sol.t_events[0])==1
    end = sol.t_events[0][0]
    clock = lambda t: brentq(lambda u:sol.sol(u)[0]-t,0,end,xtol=2e-14)
    def coefficients(u):
        _,mx,my,f = sol.sol(u)
        return (1+f*f)*mx,(1+f*f)*my,f
    # Reconstruct curvature independently by finite differences in the original
    # u variables, without copying the target back into the transfer.
    residuals = []
    for t in (-1.5,-.6,0.,.65,1.5):
        u = clock(t)
        step = 2e-6
        _,mx,my,f = sol.sol(u)
        deriv = (sol.sol(u+step)-sol.sol(u-step))/(2*step)
        s = 1+f*f
        cs,sn = np.cos(f*f),np.sin(f*f)
        rot = np.array([[cs,-sn],[sn,cs]])
        recovered = -rot@(s*np.eye(2)+J2)@deriv[1:3]/deriv[0]
        np.testing.assert_allclose(recovered,[tidal_profile(t,deformation),0.],atol=4e-8)
        trace = mx*mx+my*my-deriv[3]**2/s
        assert abs(trace)<5e-8
        residuals.append(float(np.max(np.abs(recovered-[tidal_profile(t,deformation),0.]))))
    sampled = sol.sol(np.linspace(0,end,201))
    assert np.min(np.hypot(sampled[1],sampled[2]))>.2
    return clock,coefficients,end,max(residuals)


def transfer(clock,coefficients,end,k,interval=(-1.4,1.4),tight=False):
    start,stop=map(clock,interval)
    assert start-k/2>0 and stop+k/2<end
    def flow(u,flat):
        ap,bp,fp=coefficients(u+k/2)
        am,bm,fm=coefficients(u-k/2)
        def kinetic(sign):
            ordinary=np.array([1.,sign])
            extra=np.array([fp,sign*fm])
            return (np.outer(ordinary,ordinary)+np.outer(extra,extra))/k
        qq = np.diag([ap,-am])+kinetic(-1.)
        pp = np.diag([-ap,am])+kinetic(1.)
        qp = np.diag([bp,bm])
        generator=np.block([[qq,qp],[qp,pp]])
        return (J4@generator@flat.reshape(4,4)).ravel()
    sol = solve_ivp(flow,(start,stop),np.eye(4).ravel(),method="DOP853",
                    rtol=4e-13 if tight else 8e-12,atol=1e-14 if tight else 4e-13)
    assert sol.success
    M=sol.y[:,-1].reshape(4,4)
    np.testing.assert_allclose(M.T@J4@M,J4,atol=3e-8)
    return M


def relative_vacuum_probability(first, second):
    # For a pure Gaussian with covariance I/2, diagonalize the relative
    # symplectic transformation instead of subtracting large covariances.
    relative = np.linalg.solve(first,second)
    singular = np.linalg.svd(relative,compute_uv=False)
    np.testing.assert_allclose(singular*singular[::-1],1.,atol=2e-7)
    return float(np.exp(-.5*np.sum(np.log((1+singular**2)/2))))


def null_tube():
    models = [matrix_background(d) for d in (0.,1.)]
    output=[]
    for k in (.025,.045):
        maps=[transfer(*model[:3],k) for model in models]
        verified=[transfer(*model[:3],k,tight=True) for model in models]
        for first,second in zip(maps,verified):
            np.testing.assert_allclose(first,second,rtol=3e-9,atol=6e-8)
        # Both matrix preparations are also identical before the core.
        before=[transfer(*model[:3],k,interval=(-1.7,-1.3)) for model in models]
        np.testing.assert_allclose(before[0],before[1],atol=2e-8)
        prob=relative_vacuum_probability(*maps)
        np.testing.assert_allclose(prob,relative_vacuum_probability(*verified),rtol=5e-8)
        assert 0<prob<.999
        output.append(dict(k=k,overlap_squared=prob,equal_branch_probe_purity=float((1+prob)/2),
                           common_incoming_matrix_error=float(np.max(np.abs(before[0]-before[1]))),
                           symplectic_error=max(float(np.max(np.abs(m.T@J4@m-J4))) for m in maps)))
    return dict(cap_height=[tidal_profile(0.,d) for d in (0.,1.)],
                flux_tests=output,curvature_check_max=[m[3] for m in models])


def singular_metric():
    # The signed triplet is odd around its zero, so a(t) is smooth on both
    # sides even though the inferred scalar geometry loses its lapse there.
    def ordinary(t,state):
        a,v=state
        return [v,-2*a**3]
    bg=solve_ivp(ordinary,(0.,1.5),[0.,1.],method="DOP853",dense_output=True,
                 rtol=3e-13,atol=2e-15,max_step=.03)
    def a(t):
        return np.sign(t)*bg.sol(abs(t))[0]
    def mode(j,ell,k,width=.5):
        norm=j*(j+1)
        def frequency_sq(t):
            plus,minus=a(t+k/2),a(t-k/2)
            return norm*(.8*k)**2+norm*(plus-minus)**2+plus*minus*ell*(ell+1)
        def ode(t,x):
            w=frequency_sq(t)
            return [x[1],-w*x[0],x[3],-w*x[2]]
        transfer=solve_ivp(ode,(-width,width),[1.,0.,0.,1.],method="DOP853",rtol=2e-12,atol=1e-14)
        m=transfer.y[:,-1].reshape(2,2).T
        w=np.sqrt(frequency_sq(width))
        occupation=(m[0,0]**2+m[1,1]**2+(w*m[0,1])**2+(m[1,0]/w)**2-2)/4
        exact=norm*(.8*k)**2+(4*norm-ell*(ell+1))*a(k/2)**2
        np.testing.assert_allclose(frequency_sq(0),exact,atol=1e-13)
        np.testing.assert_allclose(np.linalg.det(m),1.,atol=1e-11)
        return dict(j=j,ell=ell,k=k,endpoint_width=width,frequency_sq_at_zero=float(exact),mean_out_quanta=float(occupation),
                    determinant=float(np.linalg.det(m)))
    examples = [mode(8,ell,k) for ell,k in ((1,0.),(2,.06),(16,.06))]
    # At fixed physical longitudinal momentum the angular tower becomes light
    # simultaneously at the emergent singularity. Compare exact mode transport
    # to the local parabolic crossing; no continuum Fock space is assumed.
    tower = []
    for ell in (16,32,64,128,256):
        j = ell
        for p in (0.,.5,1.):
            k = p/np.sqrt(j*(j+1))
            record = mode(j,ell,k)
            rate = np.sqrt(ell*(ell+1.))
            estimate = np.exp(-np.pi*record["frequency_sq_at_zero"]/rate)
            tower.append(dict(j=j,ell=ell,p=p,local_parabolic=float(estimate),
                              exact_quanta=record["mean_out_quanta"]))
    endpoint = [mode(128,128,.5/np.sqrt(128*129),w) for w in (.35,.7)]
    # One zero-longitudinal-momentum cell, all nonconstant real angular modes.
    # Subtract the out-vacuum energy and retain the standard angular multiplicities.
    full_shell = [mode(32,ell,0.) for ell in range(1,65)]
    shells = []
    for j in (4,8,16,32):
        energy=sum((2*row["ell"]+1)*abs(a(.5))*np.sqrt(row["ell"]*(row["ell"]+1))
                   *row["mean_out_quanta"] for row in full_shell[:2*j])
        shells.append(dict(j=j,angular_modes=(2*j+1)**2-1,produced_energy=float(energy),
                           energy_over_spin_trace=float(energy/((2*j+1)*j*(j+1)))))
    return dict(examples=examples,angular_tower=tower,alternate_endpoints=endpoint,
                k_zero_angular_energy=shells)


def self_consistent_shell(j, coupling, transverse):
    """One real adjoint polarization in one longitudinal cell, with radial backreaction."""
    ell=np.arange(1,2*j+1,dtype=float)
    lam=ell*(ell+1)
    multiplicity=2*ell+1
    inertia=(2*j+1)*j*(j+1)
    initial_pos=np.array([.6,0.])
    initial_vel=np.array([-.8,transverse])
    omega=.6*np.sqrt(lam)
    # Real and imaginary mode functions are a centered pure Gaussian.
    init=np.r_[initial_pos,initial_vel,1/np.sqrt(2*omega),np.zeros(len(ell)),
               np.zeros(len(ell)),-np.sqrt(omega/2)]
    def unpack(state):
        pos,vel=state[:2],state[2:4]
        re,im,dr,di=np.split(state[4:],4)
        return pos,vel,re,im,dr,di
    def rhs(t,state):
        pos,vel,re,im,dr,di=unpack(state)
        radius_sq=pos@pos
        response=coupling/inertia*np.dot(multiplicity*lam,re**2+im**2)
        return np.r_[vel,-(2*radius_sq+response)*pos,dr,di,-lam*radius_sq*re,-lam*radius_sq*im]
    def crossing(t,state):
        return state[0]
    def turning(t,state):
        return state[:2]@state[2:4]
    turning.direction=1
    sol=solve_ivp(rhs,(0.,1.35),init,events=(crossing,turning),method="DOP853",
                  dense_output=True,rtol=7e-12,atol=1e-13)
    assert sol.success
    def invariants(state):
        pos,vel,re,im,dr,di=unpack(state)
        r2=pos@pos
        field=np.dot(multiplicity,dr**2+di**2+lam*r2*(re**2+im**2))
        return (vel@vel+r2*r2+coupling/inertia*field,
                pos[0]*vel[1]-pos[1]*vel[0],re*di-im*dr)
    energy,L,W=invariants(init)
    deviations=[]
    for t in np.linspace(0,1.35,61):
        current= invariants(sol.sol(t))
        deviations.append(abs(current[0]/energy-1))
        np.testing.assert_allclose(current[1],L,atol=4e-11)
        np.testing.assert_allclose(current[2],W,atol=3e-10)
    assert max(deviations)<1e-9
    if transverse==0.:
        clock=float(sol.t_events[0][0])
        assert clock<.6/.8 and sol.sol(clock)[2]<-.8
        return dict(j=j,coupling=coupling,L=float(L),crossing_clock=clock,
                    inward_speed_at_zero=float(-sol.sol(clock)[2]),max_energy_error=max(deviations))
    clock=float(sol.t_events[1][0])
    smallest=float(np.linalg.norm(sol.sol(clock)[:2]))
    bound=float(abs(L)/np.sqrt(energy))
    assert smallest>=bound
    return dict(j=j,coupling=coupling,L=float(L),radius_min=smallest,
                lower_radius_bound=bound,first_turn_clock=clock,max_energy_error=max(deviations))


def quantum_geometry(charge, size, packets_only=False):
    """Quantize both collective triplets and the three real ell=1 material modes."""
    def square_radius(n,alpha):
        idx=np.arange(n,dtype=float)
        side=-np.sqrt((idx[:-1]+1)*(idx[:-1]+alpha+1))
        return sparse.diags([side,2*idx+alpha+1,side],[-1,0,1],format="csr")
    def kinetic(radius,alpha):
        return sparse.diags(2*(2*np.arange(size)+alpha+1))-radius
    alpha=float(abs(charge))
    extended=square_radius(size+1,alpha)
    x2=extended[:size,:size]
    # The next radial basis state contributes to the top diagonal of x^4.
    x4=(extended@extended)[:size,:size]
    y2=square_radius(size,.5)
    ident=sparse.eye(size,format="csr")
    kin=(sparse.kron(kinetic(x2,alpha),ident)+sparse.kron(ident,kinetic(y2,.5)))/2
    pot=(sparse.kron(x4,ident)+2*sparse.kron(x2,y2))/2
    H=(kin+pot).tocsr()
    nodes,weights=np.polynomial.legendre.leggauss(40)
    idx=np.arange(size)
    norm=np.sqrt(2*np.exp(special.gammaln(idx+1)-special.gammaln(idx+alpha+1)))
    def near_origin(eps,amplitudes):
        rr=(nodes+1)*eps/2
        radial=np.array([special.eval_genlaguerre(n,alpha,rr**2) for n in idx]).T
        radial*=norm[None,:]*np.exp(-rr**2/2)[:,None]*(rr**alpha)[:,None]
        density=np.sum(np.abs(radial@amplitudes)**2,axis=1)
        return float((eps/2)*np.dot(weights,rr*density))
    result=dict(charge=charge,basis=size)
    if not packets_only:
        guess=np.zeros(size*size)
        guess[0]=1.
        eigen,vector=eigsh(H,k=1,which="SA",v0=guess,tol=3e-12)
        state=vector[:,0]
        energy=float(eigen[0])
        residual=float(np.linalg.norm(H@state-energy*state))
        assert residual<3e-9
        coeff=state.reshape(size,size)
        p_small,p_big=near_origin(.05,coeff),near_origin(.1,coeff)
        singular=np.linalg.svd(coeff,compute_uv=False)
        result.update(energy=energy,residual=residual,
                      virial_relative=float(abs(state@(kin@state)-2*state@(pot@state))/energy),
                      probability_below_0p05=p_small,probability_below_0p1=p_big,
                      doubled_radius_exponent=float(np.log2(p_big/p_small)),
                      geometry_purity=float(np.sum(singular**4)))

    if charge in (0,1) and size>=20:
        # Equal initial geometry densities and energies, opposite radial currents.
        # A quadratic phase gives exact radial Laguerre projection coefficients.
        t=.25
        propagator=(-1j*t)*H
        generator_trace=propagator.diagonal().sum()
        read=[]
        for chirp in (1.5,-1.5):
            z=1+1j*chirp/2
            radial=(np.exp((special.gammaln(idx+alpha+1)-special.gammaln(idx+1)
                            -special.gammaln(alpha+1))/2)*(z-1)**idx/z**(idx+alpha+1))
            psi=np.zeros((size,size),dtype=complex)
            psi[:,0]=radial/np.linalg.norm(radial)
            initial=psi.ravel()
            evolved=expm_multiply(propagator,initial,traceA=generator_trace)
            np.testing.assert_allclose(np.linalg.norm(evolved),1.,atol=2e-13)
            read.append(dict(chirp=chirp,initial_probability=near_origin(.2,psi),
                             energy=float(np.vdot(initial,H@initial).real),
                             later_probability=near_origin(.2,evolved.reshape(size,size))))
        np.testing.assert_allclose(read[0]["energy"],read[1]["energy"],atol=1e-13)
        np.testing.assert_allclose(read[0]["initial_probability"],read[1]["initial_probability"],atol=1e-14)
        assert read[0]["later_probability"]>read[1]["later_probability"]
        result["wavepackets"]=dict(clock=t,radius=.2,preparations=read)
    return result


def main():
    result=dict(spherical_crossing=singular_metric(),schwarzschild_null_tube=null_tube(),
                self_consistent=[self_consistent_shell(j,g,v) for j,g,v in
                                 ((8,.05,0.),(16,1.,0.),(32,1.,0.),(16,1.,.35),(32,1.,.35))])
    result['quantized_geometry']=[quantum_geometry(m,size) for m in (0,1,2) for size in (12,20,30)]
    for lower,high in zip(result['quantized_geometry'][1::3],result['quantized_geometry'][2::3]):
        assert abs(lower['energy']-high['energy'])<5e-6
        assert high['virial_relative']<5e-5 and .5<high['geometry_purity']<1.
        assert abs(high['doubled_radius_exponent']-(2*high['charge']+2))<.07
    result["wavepacket_refinement"]=[quantum_geometry(m,size,packets_only=True)
                                     for m in (0,1) for size in (48,64)]
    for coarse,fine in zip(result["wavepacket_refinement"][::2],result["wavepacket_refinement"][1::2]):
        pairs=zip(coarse["wavepackets"]["preparations"],fine["wavepackets"]["preparations"])
        for left,right in pairs:
            assert abs(left["later_probability"]-right["later_probability"])<1.5e-4
    dest=ROOT/"verification/cat-singular-clock-results.json"
    dest.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf8")
    print("Verified matrix transport, two Schwarzschild tidal continuations, matter backreaction and joint quantum evolution.")


if __name__=="__main__":
    main()
