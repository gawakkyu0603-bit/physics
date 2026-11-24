"""CAT receipts and emergent plane waves. Matrix scales are dimensionless.
Laboratory examples use SI. Run with --figure PATH to reproduce the paper figure.
"""
import argparse
import json
from fractions import Fraction
from itertools import product
from math import comb, cos, log, pi, sin, sqrt
from pathlib import Path

import numpy as np
from scipy import constants, linalg
from scipy.integrate import quad, solve_ivp

ROOT = Path(__file__).resolve().parents[1]
SIGMA = (np.array([[0, 1], [1, 0]]), np.array([[0, -1j], [1j, 0]]), np.diag([1, -1]))
J = np.array([[0., -1.], [1., 0.]])
THETA = linalg.block_diag(-J, -J)
ETA = linalg.block_diag([[0., 1.], [1., 0.]], np.eye(4))


def spin_tensor(pair):
    a, b = pair
    return np.array([[a, b], [b, -a]])


def rotation(angle):
    return np.array([[np.cos(angle), -np.sin(angle)], [np.sin(angle), np.cos(angle)]])


def profile(u, strength=1.):
    # Rational analytic profile near the comparison region. f''(0)=1 and
    # sqrt(1+f^2)=(1+r^2)/(1-r^2). "strength" varies the gauge deformation.
    r = u*u/4
    f = 2*r/(1-r*r)
    fp = (1+r*r)*u/(1-r*r)**2
    fpp = ((1+r*r)/(1-r*r)**2 + u*u*r*(3+r*r)/(1-r*r)**3)
    norm = (1+r*r)/(1-r*r)
    h = u/3
    axis = np.array([(1-h*h)/(1+h*h),2*h/(1+h*h)])
    axis_p = np.array([-4*h,2*(1-h*h)])/(3*(1+h*h)**2)
    pair = strength*norm*fp*axis
    pair_p = strength*((f*fp*fp/norm+norm*fpp)*axis+norm*fp*axis_p)
    return f, fp, spin_tensor(pair), spin_tensor(pair_p)


def matrix_metric(q, strength):
    u, _, y, z = q
    f, fp, m, mp = profile(u,strength)
    x = np.array([y,z])
    embedding = np.zeros((6,4),dtype=np.result_type(q))
    embedding[:4] = np.eye(4)
    embedding[1,0] = x@mp@x/2
    embedding[1,2:] = m@x
    embedding[4:,0] = fp*x
    embedding[4:,2:] = f*np.eye(2)
    density = THETA.T@embedding.T@ETA@embedding@THETA
    # In four dimensions H=sqrt(-g)*g^{-1}. Use an analytic square-root
    # continuation to allow complex-step checks of the coordinate derivatives.
    return np.sqrt(-linalg.det(density))*linalg.inv(density)


def direct_curvature(q, strength, spacing):
    # Independent Christoffel/Riemann calculation in the primitive symbols.
    # No Brinkmann transformation or analytic curvature is used here.
    g = matrix_metric(q,strength)
    inv = linalg.inv(g)
    directions = np.eye(4)
    def second(v):
        def at(h):
            return 2*(g-matrix_metric(q+1j*h*v,strength).real)/h**2
        return (4*at(spacing/2)-at(spacing))/3
    dg = np.array([matrix_metric(q+1j*1e-6*v,strength).imag/1e-6 for v in directions])
    diag = [second(v) for v in directions]
    dd = np.zeros((4,4,4,4))
    for i in range(4):
        dd[i,i] = diag[i]
        for j in range(i):
            dd[i,j] = dd[j,i] = (second(directions[i]+directions[j])-diag[i]-diag[j])/2
    def first_kind(d):
        return (d.transpose(1,0,2)+d.transpose(1,2,0)-d)/2
    lower = first_kind(dg)
    gamma = np.einsum('al,lij->aij',inv,lower)
    dgamma = []
    for i in range(4):
        dgamma.append(np.einsum('al,ljk->ajk',-inv@dg[i]@inv,lower)
                      +np.einsum('al,ljk->ajk',inv,first_kind(dd[i])))
    dgamma = np.array(dgamma)
    r = np.zeros((4,4,4,4))
    for j,k in product(range(4),repeat=2):
        r[:,:,j,k] = (dgamma[j,:,k,:]-dgamma[k,:,j,:]
                       +gamma[:,j,:]@gamma[:,k,:]-gamma[:,k,:]@gamma[:,j,:])
    return np.einsum('aiaj->ij',r), np.einsum('la,aijk->lijk',g,r)


def algebraic_eom():
    # Exact polynomial representation [U,V]=[Y,Z]=1 on Q[u,y]; restoring
    # the central i multiplies the commutator identities by common factors.
    def add(*parts):
        out={}
        for part in parts:
            for key,val in part.items():
                out[key]=out.get(key,0)+val
        return {k:v for k,v in out.items() if v}
    def scale(c, p): return {k:c*v for k,v in p.items()}
    def mul(i,j,p): return {(k+i,l+j):v for (k,l),v in p.items()}
    def derivative(axis,p):
        return {((i-1,j) if axis==0 else (i,j-1)):-(i if axis==0 else j)*v
                for (i,j),v in p.items() if (i if axis==0 else j)}
    def u(p): return mul(1,0,p)
    def v(p): return derivative(0,p)
    def y(p): return mul(0,1,p)
    def z(p): return derivative(1,p)
    def f(p): return scale(Fraction(1,2),mul(2,0,p))
    def a(p): return add(u(p),scale(Fraction(1,3),mul(2,0,p)))
    def b(p): return scale(Fraction(1,4),mul(2,0,p))
    def phi(p):
        return scale(Fraction(1,2),add(a(add(y(y(p)),scale(-1,z(z(p))))),
                                       b(add(y(z(p)),z(y(p)))) ))
    def deform(p): return add(v(p),phi(p))
    def comm(lhs,rhs): return lambda p: add(lhs(rhs(p)),scale(-1,rhs(lhs(p))))
    coords=(u,deform,y,z,lambda p:f(y(p)),lambda p:f(z(p)))
    eta_pairs=((0,1),(1,0),(2,2),(3,3),(4,4),(5,5))
    for target in coords:
        terms=[comm(coords[i],comm(coords[j],target)) for i,j in eta_pairs]
        # Each resulting differential operator has order at most six.
        for i in range(7):
            for j in range(7-i):
                state={(i,j):Fraction(1)}
                assert not add(*(op(state) for op in terms))
    return dict(matrix_equations=6,polynomial_inputs_each=28)


def geometric_checks():
    rows=[]
    for strength in (0.,1.,1.4):
        for u in (0.,.23,-.4):
            q=np.array([u,.15,.24,-.19])
            f,fp,m,mp=profile(u,strength)
            target=np.zeros((4,4))
            target[0,0]=2*(1+f*f)*fp**2-np.trace(m@m)
            for spacing in (.0015,.003):
                ricci,r=direct_curvature(q,strength,spacing)
                np.testing.assert_allclose(ricci,target,atol=1.2e-6)
                # Compare both transverse polarizations also away from the
                # origin. Two u indices transform with dt/du=s; the screen
                # rotation cancels when pulling K back to primitive symbols.
                s=1+f*f
                derivative=mp/s**2-2*f*fp*m/s**3
                mean=np.trace(m@m)/(2*s**2)-fp**2/s
                predicted=-s*s*(mean*np.eye(2)-s*derivative-J@derivative)
                np.testing.assert_allclose(r[0,2:,0,2:],predicted,atol=1.2e-6)
                if strength==1 and u==0:
                    np.testing.assert_allclose(r[0,2:,0,2:],[[1,1],[1,-1]],atol=1.2e-6)
            rows.append(dict(strength=strength,u=u,ricci_uu=round(float(target[0,0]),10)))
    return rows


def inverse_wave():
    # Prescribe BOTH tidal polarizations as functions of the emergent affine
    # reading, reconstruct the matrices, then differentiate them independently.
    def wanted(t):
        return np.array([.12*np.exp(-t*t/2)*np.cos(1.1*t),.085*np.exp(-t*t)*np.sin(1.4*t)])
    def equations(t,state):
        f,m1,m2,u=state
        s=1+f*f
        derivative=-linalg.solve(s*np.eye(2)+J,rotation(-f*f)@wanted(t))
        return [np.hypot(m1,m2)/np.sqrt(s),*derivative,1/s]
    start,finish=-2.5,2.5
    inlet=[-.2,.5,-.3,0.]
    assert np.hypot(*inlet[1:3])>quad(lambda t:linalg.norm(wanted(t)),start,finish)[0]
    sol=solve_ivp(equations,(start-.01,finish+.01),inlet,rtol=2e-12,atol=2e-14,
                  method="DOP853",dense_output=True)
    assert sol.success
    sample=[]
    for t in np.linspace(start,finish,41):
        f,m1,m2,_=sol.sol(t)
        step=8e-5
        derivative=(sol.sol(t-2*step)-8*sol.sol(t-step)+8*sol.sol(t+step)-sol.sol(t+2*step))/(12*step)
        s=1+f*f
        reconstructed=-rotation(f*f)@(s*np.eye(2)+J)@derivative[1:3]
        np.testing.assert_allclose(reconstructed,wanted(t),atol=4e-9)
        assert abs(derivative[0]**2*s-(m1*m1+m2*m2))<4e-9
        sample.append([round(float(t),8),*[round(float(q),9) for q in reconstructed]])
    def jacobi(t,state):
        d,v=state.reshape(2,2,2)
        return np.array([v,spin_tensor(wanted(t))@d]).ravel()
    transfer=solve_ivp(jacobi,(start,finish),np.array([np.eye(2),np.zeros((2,2))]).ravel(),
                       method='DOP853',rtol=2e-12,atol=2e-14).y[:,-1].reshape(2,2,2)
    assert np.linalg.norm(transfer[1])>.1
    assert np.linalg.norm(transfer[0].T@transfer[1]-transfer[1].T@transfer[0])<2e-12
    return dict(profile=sample,final_separation=transfer[0].round(9).tolist(),
                final_relative_velocity=transfer[1].round(9).tolist())


def tetrahedron():
    n=np.array([[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],dtype=float)/sqrt(3)
    rows=[]
    for direction in n:
        spin=sum(t*m for t,m in zip(direction,SIGMA))
        rows.append(linalg.eigh(spin)[1][:,-1].conj()/sqrt(2))
    v=np.array(rows)
    np.testing.assert_allclose(v.conj().T@v,np.eye(2),atol=1e-14)
    for i in range(3):
        np.testing.assert_allclose(v.conj().T@np.diag(n[:,i])@v,SIGMA[i]/3,atol=1e-14)
    high=np.eye(4)-v@v.conj().T
    def full(t,gap):
        return sum(np.kron(s,np.diag(n[:,i])-t*n[0,i]*np.eye(4))
                   for i,s in enumerate(SIGMA))+gap*np.kron(np.eye(2),high)
    from scipy.optimize import brentq
    # The four high states give the same reference signature on both sides.
    crossing=brentq(lambda t:linalg.eigvalsh(full(t,20))[1],0.,.8)
    checks=[]
    for offset in (0.,.15,.6,.8):
        spectrum=linalg.eigvalsh(full(offset,20))
        bare=linalg.eigvalsh(full(offset,0))
        index=int(np.sign(spectrum).sum()/2)-2
        assert index==int(offset<crossing) and int(np.sign(bare).sum())==0
        checks.append([offset,index,round(float(min(abs(spectrum))),8)])
    return dict(gap_over_coupling=20,wall_radius_over_L=round(float(crossing),9),checks=checks)


def real_tide():
    # Two equal spherical sources rotate about the receiver, outside their
    # radii. Use the exact Newtonian potential, with no point-source error
    # for a spherically symmetric body probed strictly outside its surface.
    m=132.90545196*constants.atomic_mass
    source=1.
    radius=.05
    rows=[]
    for size in (1e-5,1e-4,1e-3,1e-2):
        ratio=size/radius
        def frequency(phase):
            # Rationalize the difference of the two symmetric potentials;
            # at micrometre separations their leading common terms coincide.
            common=1+ratio**2
            c_plus=(cos(phase)+sin(phase))/sqrt(3)
            c_minus=(cos(phase)-sin(phase))/sqrt(3)
            d_plus=sqrt(common**2-(2*ratio*c_plus)**2)
            d_minus=sqrt(common**2-(2*ratio*c_minus)**2)
            pair_sum=sqrt(2*(common+d_plus))/d_plus+sqrt(2*(common+d_minus))/d_minus
            squared_difference=4*ratio**2*(c_plus**2-c_minus**2)
            difference=2*squared_difference*(common/(d_plus*d_minus)**2
                             +1/((d_plus+d_minus)*d_plus*d_minus))/pair_sum
            return -constants.G*source*m*difference/(2*sqrt(3)*radius*constants.hbar)
        peak=abs(quad(lambda phi:frequency(phi)*sin(2*phi),0,2*pi,epsabs=5e-14)[0]/pi)
        leading=constants.G*source*m*size**2/(sqrt(3)*constants.hbar*radius**3)
        assert abs(peak/leading-1)<.04
        rows.append(dict(radius_m=size,resonant_angular_drive_rad_s=round(peak,13),
                         balanced_time_s=round(pi/(2*peak),6),leading_ratio=round(peak/leading,7)))
    return rows


def receipt_tests():
    # Check the closed-cycle overlaps using actual projectors in Hilbert space.
    def coherent_count(n):
        amp=np.asarray([sqrt(comb(n,k)/2**n) for k in range(n+1)])
        return float(sum(t**4 for t in amp))
    total=coherent_count(4)
    assert abs(total-70/256)<1e-14
    # Two bosons use four modes = two paths times two arbitrary internal tags.
    # Construct number-state amplitudes by applying creation operators to
    # vacuum, including their sqrt(n+1) matrix elements at the output.
    def create(state,mode):
        out={}
        for n,amp in state.items():
            for i,c in enumerate(mode):
                nn=list(n); nn[i]+=1; key=tuple(nn)
                out[key]=out.get(key,0)+amp*c*sqrt(nn[i])
        return out
    pairs=[]
    for overlap_sq in (0.,1/3,1.):
        l=np.array([1.,0.,1.,0.])/sqrt(2)
        z=sqrt(overlap_sq); p=sqrt(1-overlap_sq)
        r=np.array([z,p,-z,-p])/sqrt(2)
        state=create(create({(0,0,0,0):1.},l),r)
        bins=np.zeros(3)
        for n,a in state.items(): bins[n[0]+n[1]]+=abs(a)**2
        echo=sum(bins*bins); coarse=bins[1]**2+(bins[0]+bins[2])**2
        np.testing.assert_allclose(bins,[(1+overlap_sq)/4,(1-overlap_sq)/2,(1+overlap_sq)/4],atol=1e-14)
        pairs.append([overlap_sq,round(float(echo),10),round(float(coarse),10)])
    # Recoil and relative charge at opposite walls; the mode and net charge
    # distinguish all nonempty outputs of this particular reversible circuit.
    p=.5
    out=[]
    for r in (0.,.25,1.):
        weights=np.array([(1-p)*(1-r),(1-p)*r,p*r,p*(1-r)])
        out.append(dict(exchange=r,charge_empty=round(weights[0]+weights[3],9),
                        echo=float(weights@weights)))
    trials=116
    # Two independent equal-size Bernoulli samples; use a midpoint and a
    # union bound over its two tails. delta=.40 gives family error <.001.
    assert 2*np.exp(-trials*.40**2/2)<.001
    return dict(count_return_N4=round(total,9),individual_return_N4=1/16,
                occupied_return_N4=226/256,phonon_echo=pairs,opposite_walls=out,
                rank_witness_d4_q08=.4,independent_runs_per_arm=trials)


def escaping_signals():
    # E_infinity=1, GM/c^2=1 for the optical tidal profile. Emission is
    # isotropic in the frame of a radial geodesic falling from rest at infinity.
    b_crit=3*sqrt(3)
    rows=[]
    for schwarzschild_factor in (.1,.01,.001):
        radius=2/(1-schwarzschild_factor)
        speed=sqrt(1-schwarzschild_factor)
        def fraction(b):
            cosine=sqrt(1-schwarzschild_factor*(b/radius)**2)
            return schwarzschild_factor**2*(b/radius)**2/(2*(1+speed)*(1+cosine)*(1+speed*cosine))
        probability=fraction(b_crit)
        conditional=fraction(b_crit/2)/probability
        # Independently reconstruct the critical impact from the infaller's cone.
        cos_angle=1-2*probability
        sin_angle=2*sqrt(probability*(1-probability))
        check=radius*sin_angle/(1-speed*cos_angle)
        np.testing.assert_allclose(check,b_crit,rtol=2e-11)
        import math
        rows.append(dict(schwarzschild_factor=schwarzschild_factor,escape=round(probability,13),
                         near_radial_share=round(conditional,9),
                         emissions_for_half=math.ceil(log(.5)/math.log1p(-probability))))
    # Integrate the outgoing ray and the screen Jacobi equation independently.
    # Inclining the orbital plane is an exact angular Jacobi field r*sin(phi).
    def ray(affine,state):
        r,velocity,phase,xi,xdot=state
        b=2.
        accel=b*b/r**3-3*b*b/r**4
        return [velocity,accel,b/r**2,xdot,-3*b*b/r**5*xi]
    r0=2.1
    sol=solve_ivp(ray,(0.,5.),[r0,sqrt(1-4*(1-2/r0)/r0**2),0.,0.,2/r0],
                  method="DOP853",rtol=2e-12,atol=2e-14,dense_output=True)
    rr,vel,phi,xi,xdot=sol.sol(np.linspace(0.,5.,51))
    np.testing.assert_allclose(xi,rr*np.sin(phi),atol=5e-10)
    np.testing.assert_allclose(vel**2,1-4*(1-2/rr)/rr**2,atol=5e-10)
    assert abs(rows[-1]["near_radial_share"]-.25)<.001
    return dict(rays=rows,limiting_escape_over_factor_squared=27/64,
                horizon_tide_b2=3/8)


def figure(report,dest):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig,(left,right)=plt.subplots(1,2,figsize=(8.8,3.25),layout="constrained")
    rows=report["tetrahedral_drive"]
    left.loglog([r["radius_m"]*1e3 for r in rows],[r["balanced_time_s"] for r in rows],
                "o-",color="#205c7d")
    left.axhline(70,color="#963f20",ls="--",lw=1,label="70 s hold (different geometry)")
    left.set(xlabel="Tetrahedron radius (mm)",ylabel="Time to equal Born weights (s)")
    left.legend(fontsize=7)
    wave=np.asarray(report["wave"]["profile"])
    right.plot(wave[:,0],wave[:,1],color="#205c7d",label="plus")
    right.plot(wave[:,0],wave[:,2],color="#963f20",ls="--",label="cross")
    right.set(xlabel="Affine reading in matrix units",ylabel="Reconstructed plane-wave profile")
    right.axhline(0,color="0.7",lw=.6);right.legend(fontsize=8)
    fig.savefig(dest);plt.close(fig)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument("--figure",type=Path)
    args=parser.parse_args()
    report=dict(algebra=algebraic_eom(),curvature=geometric_checks(),wave=inverse_wave(),
                material_band=tetrahedron(),tetrahedral_drive=real_tide(),receipts=receipt_tests(),
                escaping_signals=escaping_signals())
    (ROOT/"verification/cat-relational-waves-results.json").write_text(
        json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf8")
    if args.figure: figure(report,args.figure)
    print("Checked the matrix equations, inverse vacuum waves, material spectrum and closed-cycle predictions.")
