"""Physical matrix fluctuations of a receiver and orbital records of two tidal cores."""
import json
import os
from pathlib import Path

if __name__ == "__main__":
    for name in ("OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS", "OMP_NUM_THREADS"):
        os.environ[name] = "1"

import numpy as np
from scipy import linalg
from scipy.integrate import quad, solve_ivp
from scipy.optimize import brentq
from scipy.special import erf

from cat_core_multiplet import matched_caps, polarized_transfer, spin_matrices
from cat_singular_clock import J4, transfer
from cat_timelike_receiver import radius, velocity


ROOT = Path(__file__).resolve().parents[1]
CROSSING, SHIFT, SEPARATION, COUPLING_SQ = 1.95, .45, .75, .16


def material(j, point=False):
    """Compare states on precisely the same read interval as the preceding appendix."""
    left_wall = radius(CROSSING + SHIFT/2)
    right_wall = radius(CROSSING - SHIFT/2)
    frequency = np.hypot(SEPARATION, np.sqrt(j*(j+1))*(right_wall-left_wall))
    gap = (frequency+SEPARATION)/(2*(j+1))
    coefficient = j if point else 1

    def geometry(t):
        left, right = radius(t+SHIFT/2), radius(t-SHIFT/2)
        center = -coefficient*left_wall-.4*(t-CROSSING)
        return left, right, center

    def crossing_value(t):
        left, _, center = geometry(t)
        return coefficient*left+center

    start = brentq(lambda t:crossing_value(t)-gap, CROSSING-.5, CROSSING)
    finish = brentq(lambda t:crossing_value(t)+gap, CROSSING, CROSSING+.5)
    return geometry, gap, start, finish


def extremal_growth(j, mode):
    point = mode == "point"
    geometry, gap, start, finish = material(j, point)
    separation = 1.25 if mode == "screened" else gap
    multiplicity = j if point else 2*j-1 if mode == "opposite" else 1

    def frequency_sq(t):
        w, _, center = geometry(t)
        axial = (j if point else 1)*w + center
        return axial**2+separation**2-multiplicity*w**2

    def dynamics(t, z):
        return np.r_[z[2:], -frequency_sq(t)*z[:2]]

    def advance(tol):
        solution = solve_ivp(dynamics, (start, finish), [1.,0.,0.,1.], method="DOP853",
                             rtol=tol, atol=tol*1e-2)
        assert solution.success
        return solution.y[:2,-1]

    gain, impulse = advance(2e-10)
    np.testing.assert_allclose([gain,impulse], advance(1e-12), rtol=2e-9)
    # Both radii are on the monotone half period. |lambda| <= gap throughout.
    floor = multiplicity*min(abs(geometry(t)[0]) for t in (start,finish))**2-gap**2-separation**2
    comparison = np.cosh(np.sqrt(max(0.,floor))*(finish-start)) if floor>=0 else None
    if comparison is not None:
        assert gain>=comparison-1e-9
    row=dict(j=j, mode=mode, start=start, finish=finish, contact_omega_squared=frequency_sq(CROSSING),
             amplitude_gain_zero_initial_speed=gain, response_to_unit_speed=impulse, comparison_lower=comparison)
    if mode=="opposite":
        adjacent=2*j*abs(geometry(start)[0]*geometry(finish)[0])
        row["two_time_rms_product_relative_to_adjacent_bonds"]=COUPLING_SQ*abs(impulse)/adjacent
    return row


def intervals_bound(j, reference_gap=1.25, axial_offset=0.):
    """Analytic lower bounds throughout the interval, using monotone exact endpoints."""
    geometry, _, start, finish = material(j)
    spin = j-1
    gaps = []
    for a,b in zip(np.linspace(start,finish,33)[:-1],np.linspace(start,finish,33)[1:]):
        wa,ra,da = geometry(a)
        wb,rb,db = geometry(b)
        assert wb<wa<0 and rb<ra<0
        center = max(abs(da+axial_offset),abs(db+axial_offset))
        left = reference_gap**2-abs(wb)*center-wb**2/4
        # Spatial lengths of the two constituent spheres and the magnetic term.
        separated_rc = max(0.,abs(wa)*np.sqrt(spin*(spin+1))-abs(rb)*np.sqrt(j*(j+1))-center)
        right = ((reference_gap-SEPARATION)**2+separated_rc**2
                 -2*(wb**2*spin+rb**2*j))
        separated_lr = max(0.,(abs(wa)-abs(rb))*np.sqrt(j*(j+1)))
        source = SEPARATION**2+separated_lr**2-2*j*(wb**2+rb**2)
        gaps.append([left,right,source])
    return np.min(gaps, axis=0)


def direct_matrix_force():
    """Differentiate the unreduced quartic matrix force and check Gauss on rectangular links."""
    for j in (2,3):
        ref = j-1
        for orientation in (-1, 1):
            t = CROSSING-.10
            left,right,center = material(j)[0](t)
            first,second = spin_matrices(j), spin_matrices(ref)
            nl,nr = 2*j+1,2*ref+1
            # Work in native Hom(V_ref,V_j), with the tensor conjugation made explicit.
            zl,zr = np.eye(nl),np.eye(nr)
            b = [linalg.block_diag(left*x, orientation*left*y+(center if i==2 else 0)*zr)
                 for i,(x,y) in enumerate(zip(first,second))]
            b.append(linalg.block_diag(1.25*zl,0*zr))
            # Both choices have the same physical extremal index at the contact.
            if orientation==-1:
                link = np.zeros((nl,nr))
                link[0,-1]=1.
            else:
                link = np.diag(np.sqrt((2*j-np.arange(nr))*(2*j-1-np.arange(nr))))
                link = np.pad(link,((0,2),(0,0)))
                link /= np.linalg.norm(link)
            y = []
            for amplitude in (1.,-1j,0.,0.):
                top = amplitude*link
                y.append(np.block([[np.zeros((nl,nl)),top],[top.conj().T,np.zeros((nr,nr))]]))
            def comm(a,b):
                return a@b-b@a
            def force(x):
                return np.array([sum(comm(v,comm(v,a)) for v in x) for a in x])
            def projected_div(x):
                return sum(comm(v,a) for v,a in zip(x,y))
            np.testing.assert_allclose(projected_div(b),0,atol=2e-12)
            deriv = [linalg.block_diag(velocity(t+SHIFT/2)*x, orientation*velocity(t+SHIFT/2)*z
                                      +(-.4 if i==2 else 0)*zr)
                     for i,(x,z) in enumerate(zip(first,second))]+[np.zeros_like(b[-1])]
            np.testing.assert_allclose(projected_div(deriv),0,atol=2e-12)
            b,y=np.asarray(b),np.asarray(y)
            h=2e-4
            # Richardson cancels the cubic part exactly in exact arithmetic.
            diff=(8*(force(b+h*y)-force(b-h*y))-(force(b+2*h*y)-force(b-2*h*y)))/(12*h)
            expected=(left+center)**2+1.25**2-(2*j-1 if orientation==-1 else 1)*left**2
            np.testing.assert_allclose(diff,expected*y,atol=3e-9)


def axial_spin(j):
    """Bidiagonal ladder couplings in total m=-3/2, with the conjugate colour in standard form."""
    ref = j-1
    down_a = np.arange(-j,j-1)
    up_a = np.arange(-j,j-2)
    down_b, up_b = -1-down_a, -2-up_a
    assert np.all(np.abs(down_b)<=ref) and np.all(np.abs(up_b)<=ref)
    spin = np.empty(len(down_a)+len(up_a))
    spin[::2],spin[1::2]=-1.,1.
    left_z,right_z = np.empty_like(spin),np.empty_like(spin)
    left_z[::2],left_z[1::2]=-down_a,up_a
    right_z[::2],right_z[1::2]=-down_b,up_b
    edge_l,edge_r = np.zeros(len(spin)-1),np.zeros(len(spin)-1)
    edge_r[::2]=np.sqrt((ref+down_b[:-1])*(ref-down_b[:-1]+1))
    edge_l[1::2]=np.sqrt((j+down_a[1:])*(j-down_a[1:]+1))
    v = np.zeros_like(spin)
    v[::2]=(-1.)**np.arange(len(down_a))*np.sqrt((j-down_a)*(j-down_a-1))
    v/=np.linalg.norm(v)
    return spin, left_z,right_z,edge_l,edge_r,v


def tridiagonal(diagonal,edge,spinors):
    result = diagonal[:,None]*spinors
    result[1:] += edge[:,None]*spinors[:-1]
    result[:-1] += edge[:,None]*spinors[1:]
    return result


def filled_projection(diagonal,edge,transverse,vector):
    values, states=linalg.eigh_tridiagonal(diagonal,edge)
    modes=states.T@vector
    energy=np.hypot(values,transverse)
    z=np.abs(modes[:,0])**2-np.abs(modes[:,1])**2
    x=2*(modes[:,0].conj()*modes[:,1]).real
    return (np.vdot(modes,modes).real-np.sum((values*z+transverse*x)/energy))/2


def resolvent_projection(diagonal,edge,transverse,vector,nodes,dyadic=False):
    """Project onto the filled Dirac band without storing high-rank eigenvectors."""
    band=np.zeros((3,len(diagonal)),complex)
    band[0,1:]=band[2,:-1]=edge
    scale=(np.max(np.abs(diagonal))+2*np.max(np.abs(edge))+abs(transverse))/2
    grid,weights=np.polynomial.legendre.leggauss(nodes)
    if dyadic:
        # Concentrate nodes in each octave when hard and soft occupied bands coexist.
        low=abs(transverse)
        endpoints=np.r_[0.,low*2.**np.arange(int(np.ceil(np.log2(4*scale/low)))+1)]
        intervals=[((a+b+(b-a)*grid)/2,weights*(b-a)/np.pi) for a,b in zip(endpoints,endpoints[1:])]
        u=(grid+1)/2
        intervals.append((endpoints[-1]/u,weights*endpoints[-1]/(np.pi*u**2)))
    else:
        angle=(1+grid)*np.pi/4
        intervals=[(scale*np.tan(angle),weights*scale/(2*np.cos(angle)**2))]
    total=0.
    for times,quadrature in intervals:
        for t,weight in zip(times,quadrature):
            height=np.hypot(transverse,t)
            band[1]=diagonal-1j*height
            response=vector.conj().T@linalg.solve_banded((1,1),band,vector,check_finite=False)
            inverse=(response-response.conj().T)/(2j*height)
            total+=weight*(response[0,0].real-response[1,1].real+2*transverse*inverse[0,1].real)
    return (np.vdot(vector,vector).real-total)/2


def aligned_system(j, separation, axial_offset, source_gap=SEPARATION):
    geometry,_,start,finish = material(j)
    spin,z_l,z_r,e_l,e_r,v=axial_spin(j)
    scale = np.sqrt(j*(j+1))
    def coefficients(t):
        a,b,c=geometry(t)
        return (a+c+axial_offset, np.hypot(source_gap,scale*(b-a)),
                b*z_l+a*z_r-(c+axial_offset)*spin,b*e_l+a*e_r)
    def hx(diag,edge,y):
        out=tridiagonal(diag,edge,y)
        out[:,1]*=-1
        return out+(separation-source_gap)*y[:,::-1]
    return start,finish,v,coefficients,hx


def two(z,x):
    return np.array([[z,x],[x,-z]])


def aligned_absorption(j, separation, axial_offset=0., tight=False, forward_check=False):
    start,finish,v,coefficients,hx=aligned_system(j,separation,axial_offset)
    zl,omega,diag0,edge0=coefficients(start)
    init_spin=linalg.eigh(two(zl,separation))[1][:,1]
    f0=1/np.sqrt(2*omega)
    tol=3e-11 if tight else 6e-9
    def advance(fun,interval,y,dense=False):
        sol=solve_ivp(fun,interval,y,method="DOP853",rtol=tol,atol=tol*2e-3,dense_output=dense)
        assert sol.success
        return sol
    def left(t,z):
        zl,om,_,_=coefficients(t)
        return np.r_[-1j*two(zl,separation)@z[:2], z[3], -om**2*z[2]]
    ordinary=advance(left,(start,finish),np.r_[init_spin,f0,-1j*omega*f0],True)
    def source(t):
        a,b,f,_=ordinary.sol(t)
        return np.conj(f)*v[:,None]*np.array([-1j*b,1j*a])
    def adjoint(t,u):
        _,_,di,ed=coefficients(t)
        return (-1j*hx(di,ed,u.reshape(-1,2))-source(t)).ravel()
    amplitude=advance(adjoint,(finish,start),np.zeros(2*len(v),complex)).y[:,-1].reshape(-1,2)
    norm=resolvent_projection(diag0,edge0,separation-SEPARATION,amplitude,64)
    coarse=resolvent_projection(diag0,edge0,separation-SEPARATION,amplitude,48)
    np.testing.assert_allclose(coarse,norm,rtol=1e-7,atol=2e-13)
    if j<=128:
        dense=filled_projection(diag0,edge0,separation-SEPARATION,amplitude)
        np.testing.assert_allclose(dense,norm,rtol=2e-8,atol=2e-13)
    # Direct initial-value calculation with each occupied right band.
    if forward_check:
        assert j<=4
        ident=np.eye(2*len(v)).reshape(-1,len(v),2)
        h=np.array([hx(diag0,edge0,z.ravel().reshape(-1,2)).ravel() for z in ident]).T
        ev,allstates=linalg.eigh(h)
        direct=0.
        for r in allstates[:,ev<0].T:
            def flow(t,u):
                _,_,di,ed=coefficients(t)
                y=u[:-1].reshape(-1,2)
                return np.r_[(-1j*hx(di,ed,y)).ravel(),np.vdot(source(t),y)]
            direct+=abs(advance(flow,(start,finish),np.r_[r,0j]).y[-1,-1])**2
        np.testing.assert_allclose(direct,norm,rtol=3e-7,atol=1e-12)
    weight=(j+1)**2*COUPLING_SQ/(2*j+1)*norm
    def oscillator_amplitude(t):
        return abs(ordinary.sol(t)[2])
    budget=(j+1)*np.sqrt(COUPLING_SQ/(2*j+1))*quad(
        oscillator_amplitude,start,finish,epsabs=1e-11,limit=300)[0]
    correction=budget**3/6
    interval=[max(0.,np.sqrt(weight)-correction)**2,min(1.,np.sqrt(weight)+correction)**2]
    # Small independent all-order unitary evolution. The freely propagated single vacancy
    # and occupied band define the explicitly projected material/one-quantum channel.
    exact=None
    if forward_check:
        occupied=allstates[:,ev<0]
        n=occupied.shape[0]
        p=occupied.shape[1]
        collective=(j+1)*np.sqrt(COUPLING_SQ/(2*j+1))
        def exact_rhs(t,state):
            di,ed=coefficients(t)[2:]
            basis=state[:n*p].reshape(n,p)
            a=state[n*p]
            holes=state[n*p+1:]
            db=np.stack([(-1j*hx(di,ed,col.reshape(-1,2))).ravel() for col in basis.T],axis=1)
            b=collective*np.conj(basis.conj().T@source(t).ravel())
            return np.r_[db.ravel(),-1j*np.vdot(b,holes),-1j*b*a]
        end=advance(exact_rhs,(start,finish),np.r_[occupied.ravel(),1.+0j,np.zeros(p)]).y[:,-1]
        exact=float(np.vdot(end[n*p+1:],end[n*p+1:]).real)
        np.testing.assert_allclose(abs(end[n*p])**2+exact,1.,atol=2e-9)
        assert interval[0]<=exact<=interval[1]
    return dict(j=j, separation=separation, axial_offset=axial_offset, leading_weight=float(weight),
                axial_spin_dimension=len(v), axial_crossing=brentq(lambda t:coefficients(t)[0],start,finish),
                integrated_vertex_upper=budget, one_exchange_sector_all_orders=interval,
                small_rank_exact_projected=exact)


def unseeded_material(j, early, wide=False, tight=False):
    """No incident scalar. Create a compensated scalar/particle/hole from one ordinary initial state."""
    separation=1.75 if wide else 1.25
    source_gap=2*np.sqrt(j)+2 if wide else SEPARATION
    entry,finish,v,coefficients,hx=aligned_system(j,separation,0.,source_gap)
    start=0. if early else entry
    z0,om0,diag0,edge0=coefficients(start)
    init=linalg.eigh(two(z0,separation))[1][:,1]
    f0=1/np.sqrt(2*om0)
    tol=1e-11 if tight else 3e-9
    def solve(fun,interval,y,dense=False):
        sol=solve_ivp(fun,interval,y,method="DOP853",rtol=tol,atol=tol*3e-4,dense_output=dense)
        assert sol.success
        return sol
    def free(t,y):
        z,om,_,_=coefficients(t)
        return np.r_[-1j*two(z,separation)@y[:2],y[3],-om**2*y[2]]
    ordinary=solve(free,(start,finish),np.r_[init,f0,-1j*om0*f0],True)
    def drive(t):
        a,b,f,_=ordinary.sol(t)
        # On the in-vacuum the charged field creates the compensating quantum
        # with f*. The backward source consequently uses f, unlike absorption.
        return (f*v[:,None])*np.array([-1j*b,1j*a])
    def evolve(t,y,source):
        di,ed=coefficients(t)[2:]
        out=-1j*hx(di,ed,y.reshape(-1,2))
        if source:
            out-=drive(t)
        return out.ravel()
    empty=np.zeros(2*len(v),complex)
    # Carry both the full accumulation and the value up to the charge's own
    # crossing back to the same initial right Hilbert space.
    late=solve(lambda t,y:evolve(t,y,True),(finish,CROSSING),empty).y[:,-1]
    from_contact=solve(lambda t,y:evolve(t,y,True),(CROSSING,entry),empty).y[:,-1]
    from_end=solve(lambda t,y:evolve(t,y,False),(CROSSING,entry),late).y[:,-1]
    late=from_contact+from_end
    if early:
        late=solve(lambda t,y:evolve(t,y,False),(entry,start),late).y[:,-1]
        from_contact=solve(lambda t,y:evolve(t,y,False),(entry,start),from_contact).y[:,-1]
        pre=solve(lambda t,y:evolve(t,y,True),(entry,start),empty).y[:,-1]
    else:
        pre=empty
    scale=(j+1)**2*COUPLING_SQ/(2*j+1)
    def weight(y):
        # At the earlier turning point the right Dirac operator is diagonal in
        # total spin. Its large spectral range includes small eigenvalues even at high j.
        args=(diag0,edge0,separation-source_gap,y.reshape(-1,2))
        if early:
            fine=resolvent_projection(*args,10,dyadic=True)
            np.testing.assert_allclose(fine,resolvent_projection(*args,8,dyadic=True),rtol=5e-8,atol=2e-15)
            return scale*fine
        return scale*resolvent_projection(*args,64)
    late_weight,pre_weight,total=weight(late),weight(pre),weight(pre+late)
    dressing=None
    if early:
        right_energy=np.hypot(z0,separation-source_gap)
        denominator=om0+np.hypot(z0,separation)+right_energy
        virtual=1j*drive(0.).ravel()/denominator
        dressing=dict(initial=weight(virtual),contact=weight(virtual+pre+from_contact),
                      finish=weight(virtual+pre+late))
        # On a frozen background the first-order dressed occupation is constant.
        phase=np.exp(-1j*denominator*(finish-start))
        reference=drive(0.).ravel()*(1-phase)/(1j*denominator)
        np.testing.assert_allclose(weight(virtual+reference),dressing["initial"],rtol=1e-9,atol=1e-13)
    if j<=32 and early:
        np.testing.assert_allclose(total,scale*filled_projection(diag0,edge0,separation-source_gap,
                                                                 (pre+late).reshape(-1,2)),rtol=5e-8,atol=1e-12)
    counts=[]
    for t in (entry,CROSSING,finish):
        _,om,_,_=coefficients(t)
        _,_,f,df=ordinary.sol(t)
        np.testing.assert_allclose(-2*np.imag(f.conjugate()*df),1.,rtol=3e-5)
        counts.append(float(abs(np.sqrt(om/2)*f-1j*df/np.sqrt(2*om))**2))
    bound=None
    if wide:
        dmax=max(abs(material(j)[0](t)[2]) for t in (start,finish))
        bound=[separation**2-dmax-.25,(source_gap-separation)**2-2*(2*j-1),source_gap**2-4*j]
        assert min(bound)>0
    contact_weight=weight(pre+from_contact)
    one_port=None
    if early and wide:
        # Omega first rises then falls. E/Omega² decreases on the rising part
        # and E decreases on the falling part. No finite-time sampling is needed for this bound.
        omega_peak_upper=np.hypot(source_gap,SHIFT*np.sqrt(j*(j+1)))
        width_bound=omega_peak_upper/(np.sqrt(om0)*coefficients(CROSSING)[1])
        budget=CROSSING*np.sqrt(COUPLING_SQ/(2*j+1))*width_bound
        one_weight=contact_weight/(j+1)**2
        lower=max(0.,np.sqrt(one_weight)-budget**3/6)**2
        upper=(np.sqrt(one_weight)+budget**3/6)**2
        one_port=dict(first_order=one_weight,integrated_vertex_upper=budget,all_orders_in_sector=[lower,upper],
                      copy_threshold_for_positive_lower=6*np.sqrt(one_weight)/budget**3)
        if j==8:
            # Independent forward check from each initially occupied matter orbital.
            dim=2*len(v)
            unit=np.eye(dim).reshape(dim,-1,2)
            right_h=np.stack([hx(diag0,edge0,column).ravel() for column in unit],axis=1)
            values,states=linalg.eigh(right_h)
            occupied=states[:,values<0]
            holes=occupied.shape[1]
            base=occupied.size
            vertex=np.sqrt(COUPLING_SQ/(2*j+1))
            def forward(t,state):
                orbitals=state[:base].reshape(len(v),2,holes)
                di,ed=coefficients(t)[2:]
                moving=di[:,None,None]*orbitals
                moving[1:]+=ed[:,None,None]*orbitals[:-1]
                moving[:-1]+=ed[:,None,None]*orbitals[1:]
                moving[:,1]*=-1
                moving+=(separation-source_gap)*orbitals[:,::-1]
                coupling=vertex*np.conj(orbitals.reshape(dim,holes).conj().T@drive(t).ravel())
                vacuum=state[base]
                triplets=state[base+1:base+1+holes]
                return -1j*np.r_[moving.ravel(),np.vdot(coupling,triplets),coupling*vacuum,coupling]
            initial=np.r_[occupied.ravel(),1.+0j,np.zeros(2*holes)]
            readout=solve(forward,(start,CROSSING),initial).y[base:,-1]
            exact=np.linalg.norm(readout[1:1+holes])**2
            np.testing.assert_allclose(np.linalg.norm(readout[1+holes:])**2,one_weight,rtol=2e-6,atol=1e-16)
            np.testing.assert_allclose(abs(readout[0])**2+exact,1.,atol=2e-9)
            assert lower<exact<upper
            one_port["direct_projected_weight"]=float(exact)
    return dict(j=j,preparation_clock=start,source_gap=source_gap,left_gap=separation,window_start=entry,finish=finish,
                free_scalar_quanta_per_charge=counts,early_weight=pre_weight,window_weight=late_weight,
                interference=total-pre_weight-late_weight,leading_final_weight=total,
                leading_contact_weight=contact_weight,first_order_dressed=dressing,
                whole_preparation_squared_frequency_lower=bound,one_resolved_port_at_crossing=one_port)


def unseeded_time_refinement(coarse,fine):
    """Compare numerical drift with the analytic return-amplitude interval at the crossing."""
    keys=("leading_contact_weight","leading_final_weight","early_weight","window_weight","interference")
    relative={k:abs(coarse[k]-fine[k])/abs(fine[k]) for k in keys}
    single=fine["one_resolved_port_at_crossing"]
    lo,hi=single["all_orders_in_sector"]
    first_order_drift=abs(coarse["one_resolved_port_at_crossing"]["first_order"]-single["first_order"])
    fraction=first_order_drift/((hi-lo)/2)
    # Resolve the cubic return bound separately from the change in the numerical leading weight.
    assert 0<lo<=single["first_order"]<=hi and fraction<.05
    coarse_weight=coarse["one_resolved_port_at_crossing"]["first_order"]
    # Compare the tiny physical weights on an order-one scale in the archive verifier.
    # The drift is a difference of nearly equal integrals, so quote its ratio to six decimals.
    return dict(j=fine["j"],relative_time_tolerances=[3e-9,1e-11],relative_changes=relative,
                single_reference_weights_times_1e11=dict(coarse=1e11*coarse_weight,
                    fine=1e11*single["first_order"],all_orders=[1e11*lo,1e11*hi]),
                leading_weight_drift_over_return_half_width=round(float(fraction),6))


def chain_force(u, x):
    """Exact temporal-gauge matrix equations on one axial chain (no expansion in u)."""
    squares = u*u
    diagonal = np.diff(squares,prepend=0.,append=0.)
    differences = np.diff(x,axis=0)
    flux = squares[:,None]*differences
    fu = u*(.5*np.diff(diagonal)-np.einsum("ij,ij->i",differences,differences))
    fx = np.empty_like(x)
    fx[0],fx[-1]=flux[0],-flux[-1]
    fx[1:-1]=np.diff(flux,axis=0)
    return fu,fx


def chain_energy(u,x,v,p):
    magnetic=np.diff(u**2,prepend=0.,append=0.)
    return ((v@v+np.sum(p*p)+np.sum((u[:,None]*np.diff(x,axis=0))**2))/2
            +magnetic@magnetic/8)


def check_nonlinear_reduction():
    u=np.array([.3,-.45,.18,.9])
    x=np.array([[.2,.7],[-.1,.3],[.4,.1],[1.,-.2],[.8,.6]])
    def matrices(bonds, positions):
        plus=np.diag(bonds,-1)
        return np.array([(plus+plus.T)/2,(plus-plus.T)/(2j),
                         np.diag(positions[:,0]),np.diag(positions[:,1])])
    def comm(a,b):
        return a@b-b@a
    b=matrices(u,x)
    vel=matrices(np.roll(u,1),np.roll(x,1,axis=0))
    exact=np.array([-sum(comm(a,comm(a,y)) for a in b) for y in b])
    fu,fx=chain_force(u,x)
    np.testing.assert_allclose(exact,matrices(fu,fx),atol=2e-14)
    np.testing.assert_allclose(sum(comm(a,v) for a,v in zip(b,vel)),0,atol=2e-14)
    energy=(sum(np.vdot(v,v).real for v in vel)/2 +
            sum(np.vdot(comm(b[i],b[k]),comm(b[i],b[k])).real for i in range(4) for k in range(i))/2)
    np.testing.assert_allclose(energy,chain_energy(u,x,np.roll(u,1),np.roll(x,1,axis=0)),atol=2e-14)


def nonlinear_passage(j,seed,step_scale=.45):
    geom,gap,start,finish=material(j)
    left,_,center=geom(start)
    derivative=velocity(start+SHIFT/2)
    ref=j-1
    seam=2*ref
    axes=[np.arange(-ell,ell+1,dtype=float) for ell in (ref,j)]
    strengths=[np.sqrt((ell-axis[:-1])*(ell+axis[:-1]+1)) for ell,axis in zip((ref,j),axes)]
    u=np.r_[-left*strengths[0],seed,left*strengths[1]]
    v=np.r_[-derivative*strengths[0],0.,derivative*strengths[1]]
    x=np.column_stack((np.r_[-left*axes[0]+center,left*axes[1]],
                       np.r_[np.zeros(len(axes[0])),np.full(len(axes[1]),gap)]))
    p=np.column_stack((np.r_[-derivative*axes[0]-.4,derivative*axes[1]],np.zeros(len(x))))
    energy0=chain_energy(u,x,v,p)
    nstep=int(np.ceil((finish-start)*(2*j+1)/step_scale))
    dt=(finish-start)/nstep
    fu,fx=chain_force(u,x)
    guard=set(np.linspace(0,nstep,min(nstep+1,193),dtype=int))
    first_crossings=[None,None]
    previous=None
    peak=abs(u[seam])
    max_drift=0.
    for i in range(nstep+1):
        readings=[float(np.min(x[seam+1:,1])-np.max(x[:seam+1,1])),
                  float(x[seam,0]-x[seam+1,0])]
        if previous is not None:
            for k,(old,new) in enumerate(zip(previous,readings)):
                if first_crossings[k] is None and old*new<=0 and old!=new:
                    first_crossings[k]=start+dt*(i-1+old/(old-new))
        previous=readings
        peak=max(peak,abs(u[seam]))
        if i in guard:
            max_drift=max(max_drift,abs(chain_energy(u,x,v,p)/energy0-1))
        if i==nstep:
            break
        v+=dt/2*fu
        p+=dt/2*fx
        u+=dt*v
        x+=dt*p
        fu,fx=chain_force(u,x)
        v+=dt/2*fu
        p+=dt/2*fx
    return dict(j=j, initial_link=seed, steps=nstep, initial_energy=energy0/COUPLING_SQ,
                relative_energy_drift=max_drift, peak_link=float(peak),
                final_link=u[seam], final_projected_axial=readings[1], final_marker_gap=readings[0],
                first_marker_closure=first_crossings[0], first_axial_zero=first_crossings[1],
                initial_marker_gap=gap, start=start, finish=finish)


def angular_energy_bound(j,ell_min=8,transverse=1.25):
    """A finite-interval bound on the reference oscillator energy of *all* high left harmonics."""
    geom,_,start,finish=material(j)
    grid=np.linspace(start,finish,33)
    exponent=0.
    for a,b in zip(grid,grid[1:]):
        x,_,d0=geom(a)
        y,_,d1=geom(b)
        low,high=abs(x),abs(y)
        offset=max(abs(d0),abs(d1))
        alpha=1-offset/(low*ell_min)
        assert 0<alpha<1
        connection=3*((1+1.4/ell_min)/(alpha*low))**2
        rate=((offset**2+transverse**2+connection)/(low*ell_min)
              +2*offset+2*high*(1+1/ell_min)+2/low)
        exponent+=(b-a)*rate
    return float(np.exp(exponent))


def parallel_frame_check():
    """Propagate a physical mode in temporal gauge and independently in a horizontal frame."""
    ell=2
    angular=spin_matrices(ell)
    n=2*ell+1
    identity=np.eye(n)
    geom,_,start,finish=material(128)
    def coefficients(t):
        w,_,d=geom(t)
        wd=velocity(t+SHIFT/2)
        parts=[w*a-(d if k==2 else 0)*identity for k,a in enumerate(angular)]+[1.25*identity]
        diff=[wd*a+(.4 if k==2 else 0)*identity for k,a in enumerate(angular)]+[0*identity]
        D,Dt=np.vstack(parts),np.vstack(diff)
        Q=D.conj().T@D
        K=linalg.block_diag(*([Q]*4))+2*np.block([[a@b-b@a for b in parts] for a in parts])
        return D,Dt,linalg.inv(Q),K
    D,Dt,inv,K=coefficients(start)
    E=linalg.null_space(D.conj().T)
    qs=np.cos(np.arange(E.shape[1]))
    ps=np.sin(np.arange(E.shape[1]))
    y=E@qs
    p=E@ps+D@inv@Dt.conj().T@y
    npos=len(y)
    nframe=E.size
    nphys=E.shape[1]
    def equation(t,flat):
        D,Dt,inv,K=coefficients(t)
        y,p=flat[:npos],flat[npos:2*npos]
        e=flat[2*npos:2*npos+nframe].reshape(E.shape)
        q,v=flat[-2*nphys:-nphys],flat[-nphys:]
        ej=Dt.conj().T@e
        H=e.conj().T@K@e +3*ej.conj().T@inv@ej
        return np.r_[p,-K@y+D@(D.conj().T@y),(-D@inv@ej).ravel(),v,-H@q]
    sol=solve_ivp(equation,(start,finish),np.r_[y,p,E.ravel(),qs,ps],method="DOP853",
                  rtol=3e-11,atol=1e-13)
    assert sol.success
    D,Dt,inv,K=coefficients(finish)
    f=sol.y[:,-1]
    y,p=f[:npos],f[npos:2*npos]
    e=f[2*npos:2*npos+nframe].reshape(E.shape)
    gauge_coordinate=inv@D.conj().T@y
    np.testing.assert_allclose(D.conj().T@p,Dt.conj().T@y,atol=4e-10)
    np.testing.assert_allclose(e.conj().T@e,np.eye(nphys),atol=3e-10)
    np.testing.assert_allclose(D.conj().T@e,0.,atol=3e-10)
    np.testing.assert_allclose(e.conj().T@y,f[-2*nphys:-nphys],atol=4e-10)
    np.testing.assert_allclose(e.conj().T@(p-Dt@gauge_coordinate),f[-nphys:],atol=4e-10)


def normal_coordinates(relative):
    """Real symplectic basis for one hyperbolic pair and one simple elliptic pair."""
    eig,v=linalg.eig(relative)
    expand,contract=np.argmax(eig.real),np.argmin(eig.real)
    angle=np.argmax(eig.imag)
    assert eig[expand].real>1 and eig[contract].real<1 and eig[angle].imag>0
    np.testing.assert_allclose([eig[expand].imag,eig[contract].imag,abs(eig[angle])],[0.,0.,1.],atol=8e-9)
    def canonical(q,p):
        pairing=q@J4@p
        return q/np.sqrt(abs(pairing)),p*np.sign(pairing)/np.sqrt(abs(pairing))
    q1,p1=canonical(v[:,expand].real,v[:,contract].real)
    q2,p2=canonical(v[:,angle].real,v[:,angle].imag)
    basis=np.column_stack([q1,q2,p1,p2])
    np.testing.assert_allclose(basis.T@J4@basis,J4,atol=3e-9)
    form=linalg.solve(basis,relative@basis)
    rho=eig[expand].real
    values=linalg.svdvals(form)
    np.testing.assert_allclose(values,[rho,1,1,1/rho],atol=2e-8)
    return basis, float(rho), float(abs(np.angle(eig[angle])))


def orbital_fidelity(relative,symplectic_input):
    transformed=linalg.solve(symplectic_input,relative@symplectic_input)
    values=linalg.svdvals(transformed)
    scales=values[:len(values)//2]
    return float(np.prod(2/(scales+1/scales)))


def aperture_bound(rho,moment_area):
    # One window on one physical quadrature separates the histories. The integer counts
    # mathematical thresholds; it does not count copies, interactions or repeated observations.
    n=np.arange(1,200)
    bounds=np.maximum(0.,1-3*(moment_area/rho**n)**(2/3))/n
    best=np.argmax(bounds)
    assert n[best]<100 and bounds[best]>1/200
    return dict(moment_area=moment_area, intervals=int(n[best]), trace_distance_at_least=float(bounds[best]))


def gaussian_readout(rho,noise_ratio):
    scale=np.sqrt((rho*rho+noise_ratio)/(1+noise_ratio))
    threshold=np.sqrt(2*np.log(scale)/(1-1/scale**2))
    discrimination=(1+erf(threshold/np.sqrt(2))-erf(threshold/(scale*np.sqrt(2))))/2
    def density(x,s):
        return np.exp(-x*x/(2*s*s))/(np.sqrt(2*np.pi)*s)
    by_integration=.5+quad(lambda x:density(x,1.)-density(x,scale),0,threshold)[0]
    np.testing.assert_allclose([density(threshold,1.),discrimination],[density(threshold,scale),by_integration],
                               atol=2e-13)
    return dict(noise_to_input_variance=noise_ratio, threshold_in_measured_baseline_widths=threshold,
                equal_prior_success=discrimination)


def tidal_states():
    clock,coefficients,_,end=matched_caps()
    rows=[]
    pairs=[]
    arrival_weight=np.ones(2)
    angle_accum=np.zeros(2)
    for k in (.16,.16+np.sqrt(2/1056)):
        def make(tight):
            return [transfer(clock,lambda u:coefficients(u,strength)[:3],end,k,tight=tight)
                    for strength in (0.,.08)]
        maps=make(True)
        relative=linalg.solve(maps[0],maps[1])
        basis,rho,angle=normal_coordinates(relative)
        ordinary=make(False)
        _,other,other_angle=normal_coordinates(linalg.solve(ordinary[0],ordinary[1]))
        np.testing.assert_allclose([rho,angle],[other,other_angle],rtol=3e-7)
        # The same accessible outgoing quadrature scales by rho between the two cores.
        q_in=linalg.inv(basis)[0]
        q_out=linalg.solve(maps[0].T,q_in)
        np.testing.assert_allclose(q_out@maps[1],rho*q_in,rtol=2e-8,atol=2e-8)
        fplus,fminus=[coefficients(clock(1.4)+sign*k/2,0.)[2] for sign in (1,-1)]
        gradients=np.array([[1.,-1.,0,0],[0,0,1.,1.],[fplus,-fminus,0,0],[0,0,fplus,fminus]])
        material=linalg.solve(gradients.T,q_out)
        np.testing.assert_allclose(material@gradients,q_out,atol=1e-10)
        for index,strength in enumerate((0.,.08)):
            response=polarized_transfer(clock,coefficients,strength,k,direct=True)[4:6,:2]
            helicity=response[0,0]-1j*response[1,0]
            arrival_weight[index]*=abs(helicity)**2
            angle_accum[index]+=np.angle(helicity)
        # The palindromic characteristic polynomial provides an independent extraction.
        trace=np.trace(relative)
        quadratic=(trace**2-np.trace(relative@relative))/2
        roots=np.roots([1,-trace,quadratic-2])
        large=max(roots.real)
        np.testing.assert_allclose((large+np.sqrt(large**2-4))/2,rho,rtol=4e-9)
        ceiling=2/(rho+1/rho)
        np.testing.assert_allclose(orbital_fidelity(relative,basis),ceiling,atol=4e-9)
        rows.append(dict(k=k,expanding_factor=rho,elliptic_angle=angle,
                         isotropic_fidelity=orbital_fidelity(relative,np.eye(4)),
                         maximum_pure_gaussian_fidelity=ceiling,
                         normalized_material_axis_input_variance=float(np.dot(q_in,q_in)/(2*np.dot(material,material))),
                         material_axis_equal_prior=[gaussian_readout(rho,x) for x in (0.,1.,10.,100.)],
                         finite_moment_apertures=[aperture_bound(rho,a) for a in (.5,1.,5.,50.,500.)]))
        pairs.append((relative,basis))
    both=linalg.block_diag(*[entry[0] for entry in pairs])
    joint_basis=linalg.block_diag(*[entry[1] for entry in pairs])
    joint=float(np.prod([row["maximum_pure_gaussian_fidelity"] for row in rows]))
    weights=arrival_weight/arrival_weight.sum()
    loss_argument=4*np.prod(weights)*joint*np.sin(np.diff(angle_accum)[0])**2
    worst_deficit=float(loss_argument/(2*(1+np.sqrt(1-loss_argument))))
    np.testing.assert_allclose(orbital_fidelity(both,joint_basis),joint,atol=5e-9)
    # Include correlations between both charged wave packets in the input.
    sym=linalg.block_diag(J4,J4)
    i,j=np.mgrid[:8,:8]
    for t in (.02,.2,.5):
        h=np.sin((i+j+1)*.83)+np.cos((i+1)*(j+1)*.7)
        entangle=linalg.expm(t*sym@h)
        assert orbital_fidelity(both,joint_basis@entangle)<=joint+3e-9
    trains=[]
    for n in (4,8,16,32):
        coeff=np.sqrt(2/(n+1))*np.sin(np.arange(1,n+1)*np.pi/(n+1))
        fidelity=float((coeff[1:]@coeff[:-1])**2)
        np.testing.assert_allclose(fidelity,np.cos(np.pi/(n+1))**2,atol=3e-15)
        trains.append(dict(packets=n,non_gaussian_joint_fidelity=fidelity))
    return dict(single=rows,joint_pure_gaussian_ceiling=joint,non_gaussian_trains=trains,
                equal_prior_orbital_discrimination_floor=(1+np.sqrt(1-joint))/2,
                polarization_deficit_worst_pure_gaussian=worst_deficit)


def charge_index():
    results=[]
    for ell in range(1,9):
        x,y,z=spin_matrices(ell)
        n=len(z)
        def spectrum(d):
            a=z-d*np.eye(n)
            return linalg.eigvalsh(np.block([[a,x-1j*y],[x+1j*y,-a]]))
        vals=spectrum(-1)
        count=int(np.sum(abs(vals)<1e-10))
        gap=min(abs(vals[abs(vals)>1e-10]))
        change=(np.sign(spectrum(-1+1e-5)).sum()-np.sign(spectrum(-1-1e-5)).sum())/2
        assert count==(1 if ell==1 else 0) and change==count and gap>=1-1e-10
        results.append(dict(relative_spin=ell, zeros=count, jump=int(change), gap_at_contact=float(gap)))
    return results


def main():
    direct_matrix_force()
    check_nonlinear_reduction()
    parallel_frame_check()
    growth=[extremal_growth(j,mode) for j in (8,32,128,512,2048)
            for mode in ("point","opposite","aligned","screened")]
    nonlinear=[]
    for j,seed in ((32,.1),(128,.1),(512,.1),(2048,.0001),(2048,.025),(2048,.1)):
        coarse=nonlinear_passage(j,seed)
        fine=nonlinear_passage(j,seed,.225)
        np.testing.assert_allclose(fine["peak_link"],coarse["peak_link"],rtol=.002)
        for name in ("first_marker_closure","first_axial_zero"):
            if fine[name] is None:
                assert coarse[name] is None
            else:
                assert abs(coarse[name]-fine[name])<2e-4
        nonlinear.append(fine)
    absorption=[]
    for j in (2,8,32,128,512,2048):
        for separation in (material(j)[1],1.25):
            result=aligned_absorption(j,separation,forward_check=j==2)
            absorption.append(result)
    tight=aligned_absorption(2048,1.25,tight=True)
    np.testing.assert_allclose(tight["leading_weight"],absorption[-1]["leading_weight"],rtol=2e-5)
    bounds=[dict(j=j,minimum_spatial_frequency_squared_lower=intervals_bound(j).tolist(),
                 high_harmonic_reference_energy_ratio_upper=angular_energy_bound(j))
            for j in (8,32,128,512,2048)]
    assert min(bounds[2]["minimum_spatial_frequency_squared_lower"])>0
    offsets=np.arange(-2,3)*.012
    separations=1.25+.18*np.arange(5)
    banks=[aligned_absorption(128,sep,axial_offset=off) for sep,off in zip(separations,offsets)]
    among=min((separations[i]-separations[k])**2+(offsets[i]-offsets[k])**2-2*abs(offsets[i]-offsets[k])
              for i in range(5) for k in range(i))
    gap=min(min(intervals_bound(128,sep,off)) for sep,off in zip(separations,offsets))
    assert among>0 and gap>0
    contacts=[row["axial_crossing"] for row in banks]
    assert min(np.diff(contacts))>.009
    unseeded=[unseeded_material(j,early,wide) for j,early,wide in
              ((32,True,False),(128,False,False),(128,True,False),(512,False,False),
               (8,True,True),(32,True,True),(128,True,True),(512,True,True),(2048,True,True))]
    fine=unseeded_material(128,True,True,tight=True)
    base=next(row for row in unseeded if row["j"]==128 and row["whole_preparation_squared_frequency_lower"] is not None)
    np.testing.assert_allclose(base["leading_contact_weight"],fine["leading_contact_weight"],rtol=2e-5)
    high_rank=unseeded_material(2048,True,True,tight=True)
    time_refinement=unseeded_time_refinement(unseeded[-1],high_rank)
    unseeded[-1]=high_rank
    return dict(extremal=growth,nonlinear=nonlinear,charge_sectors=charge_index(),aligned_bounds=bounds,
                aligned_absorption=absorption,
                unseeded=unseeded,unseeded_time_refinement=time_refinement,
                distinct_receivers=dict(j=128,contacts=contacts,minimum_interbank_bound=among,
                                        minimum_other_link_bound=gap,
                                        leading_weight_five_single_copies=sum(row["leading_weight"] for row in banks)/129**2),
                tidal=tidal_states())


if __name__=="__main__":
    output=ROOT/"verification"/"cat-receiver-stability-results.json"
    output.write_bytes((json.dumps(main(),indent=2,allow_nan=False)+"\n").encode("utf-8"))
