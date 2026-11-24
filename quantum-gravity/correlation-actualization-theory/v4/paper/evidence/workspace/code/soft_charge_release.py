"""Local current mixing and four-dimensional endpoints for paper 2, Appendix Z."""
import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import eigh
from scipy.optimize import brentq

ROOT = Path(__file__).resolve().parents[1]


def check(a, b, tol=1e-9):
    assert abs(a-b) <= tol*max(1., abs(b)), (a, b)


def partitions(level, largest=None):
    if level == 0:
        yield ()
        return
    for label in range(min(level, largest or level), 0, -1):
        for tail in partitions(level-label, label):
            yield (label,)+tail


def matrices(n):
    states=list(partitions(n))
    labels={state: i for i, state in enumerate(states)}
    shape=(len(states),len(states))
    V=np.zeros(shape)
    counts=np.array([[s.count(k) for k in range(1,n+1)] for s in states],dtype=float)
    modes=np.arange(1,n+1,dtype=float)
    d3=counts@(modes**3)/n**3
    d5=counts@(modes**5)/n**5
    for col,state in enumerate(states):
        for parent in set(state):
            for i in range(1,parent//2+1):
                j=parent-i
                target=list(state)
                target.remove(parent)
                target.extend([i,j])
                row=labels[tuple(sorted(target,reverse=True))]
                amplitude=math.sqrt(i*j*parent*state.count(parent)*(state.count(i)+1)*
                                    (state.count(j)+1+(i==j)))/(1+(i==j))
                V[row,col]+=amplitude
                V[col,row]+=amplitude
    return states,counts,V,d3,d5


def reversible():
    rows=[]
    for n in (4,7,11,15):
        states,counts,V,_,_=matrices(n)
        eig,vec=eigh(V)
        hard=states.index((n,))
        for t in (.17,.43):
            psi=vec@(np.exp(-1j*t*eig)*vec[hard,:].conj())
            occupation=abs(psi)**2@counts
            angle=n*t
            analytic=np.array([4*(n-m)/(n*m)*math.sin(angle*m/2)**2 if m<n else
                               (math.sin(n*angle/2)/(n*math.sin(angle/2)))**2
                               for m in range(1,n+1)])
            error=float(max(abs(occupation-analytic)))
            assert error<1e-10,(n,t,error)
            check(occupation@np.arange(1,n+1),n)
            h=max(1,int(math.sqrt(n)))
            rows.append(dict(level=n,time=t,soft_modes=h,occupation_error=error,
                             soft_energy_fraction=float(occupation[:h]@np.arange(1,h+1)/n)))
    return rows


def dephasing_cost(observable):
    identity=np.eye(len(observable))
    cd=np.kron(observable,identity)-np.kron(identity,observable.T)
    return cd@cd/2


def irreversible():
    rows=[]
    for n in (4,6,8):
        states,counts,V,d3,d5=matrices(n)
        dim=len(states)
        magnitude=max(abs(np.linalg.eigvalsh(V)))
        scaled=V/magnitude
        generator=dephasing_cost(scaled)
        dx3=d3[:,None]-d3[None,:]
        dx5=d5[:,None]-d5[None,:]
        diag=(dx3**2+dx5**2).ravel()/2
        generator[np.diag_indices(dim*dim)]+=diag
        eig,vec=eigh(generator)
        assert abs(eig[0])<1e-13 and eig[1]>1e-9
        v_bound=float(np.sum(V**2*(dx3**2+dx5**2))/2/np.sum(V**2))
        assert eig[1]<=v_bound+1e-10
        initial=np.zeros((dim,dim))
        hard=states.index((n,))
        initial[hard,hard]=1
        # A single unit of each of the three normalized noise rates is used for this diagnostic.
        stationary=np.eye(dim)/dim
        check(float(np.linalg.norm(generator@stationary.ravel())),0)
        t=2/eig[1]
        final=(vec@(np.exp(-eig*t)*(vec.T@initial.ravel()))).reshape((dim,dim))
        close_to_equilibrium=float(np.linalg.norm(final-stationary))
        assert np.linalg.eigvalsh(final)[0]>-1e-12
        check(float(np.trace(final)),1)
        # Traceless Hermitian gap eigenoperators need not always be real symmetric.
        matrix=vec[:,1].reshape((dim,dim))
        slow=(matrix+matrix.T)/2
        if np.linalg.norm(slow)<.1:
            slow=(matrix-matrix.T)/(2j)
        slow=slow-np.trace(slow)/dim*np.eye(dim)
        spectrum,unit=eigh(slow)
        scale=spectrum.clip(min=0).sum()
        plus=(unit*(spectrum.clip(min=0)/scale)[None,:])@unit.conj().T
        minus=(unit*((-spectrum).clip(min=0)/scale)[None,:])@unit.conj().T
        assert np.linalg.norm(plus@minus)<1e-8
        result=(vec@(np.exp(-eig*t)*(vec.T@(plus-minus).ravel()))).reshape((dim,dim))
        trace_distance=float(np.sum(abs(np.linalg.eigvalsh(result)))/2)
        check(trace_distance,math.exp(-2),1e-8)
        rows.append(dict(level=n,dimension=dim,gap=float(eig[1]),trial_bound=v_bound,
                         normalized_cubic_norm=magnitude,hard_state_HS_error=close_to_equilibrium,
                         distinguishability_at_two_relaxation_times=trace_distance))
    return rows


def partition_counts(top):
    # Euler's pentagonal recursion uses integers throughout.
    p=[1]+[0]*top
    for n in range(1,top+1):
        j=1
        while j*(3*j-1)//2<=n:
            sign=1 if j%2 else -1
            for g in (j*(3*j-1)//2,j*(3*j+1)//2):
                if g<=n:
                    p[n]+=sign*p[n-g]
            j+=1
    return p


def rayleigh_bound(n,p):
    numer3=0
    numer5=0
    total=0
    for h in range(2,n+1):
        for i in range(1,h//2+1):
            j=h-i
            # [t^(n-h)] P(t)/((1-t^i)(1-t^j)(1-t^h)).
            count=p[:n-h+1]
            for part in (i,j,h):
                for m in range(part,len(count)):
                    count[m]+=count[m-part]
            # Twice the squared matrix element summed over all allowed incoming partitions.
            weight=(2*i*j*h//(1+(i==j)))*count[-1]
            total+=weight
            numer3+=weight*(h**3-i**3-j**3)**2
            numer5+=weight*(h**5-i**5-j**5)**2
    return numer3/(2*total*n**6), numer5/(2*total*n**10)


def counting():
    p=partition_counts(6400)
    labels={}
    for h in range(2,200):
        for i in range(1,h//2+1):
            j=h-i
            key=(h**3-i**3-j**3,h**5-i**5-j**5)
            assert key not in labels
            labels[key]=(i,j)
    assert (6**3-5**3-1)==(5**3-3**3-2**3)
    trial=[]
    for n in (4,6,8,16,32,64,128,192):
        r3,r5=rayleigh_bound(n,p)
        if n<=8:
            _,_,V,d3,d5=matrices(n)
            for val,diag in ((r3,d3),(r5,d5)):
                check(val,float(np.sum(V**2*(diag[:,None]-diag[None,:])**2)/(2*np.sum(V**2))))
        trial.append(dict(level=n,number_of_partitions=str(p[n]),cubic_moment_bound=r3,fifth_moment_bound=r5))
    thermal=[]
    for n in (100,400,1600,6400):
        beta=math.pi/math.sqrt(6*n)
        for scale in (.55,1.1,2.):
            m=max(1,round(scale/beta))
            occ=sum(p[n-k] for k in range(m,n+1,m))/p[n]
            next_occ=sum(p[n-m-k] for k in range(m,n-m+1,m))/p[n-m]
            check(occ,(1+next_occ)*p[n-m]/p[n])
            thermal.append(dict(level=n,mode=m,mean_occupation=occ,
                                limiting_occupation=1/math.expm1(beta*m),
                                paired_emission_over_lower_absorption=(p[n-m]/p[n])**2,
                                grand_canonical_ratio=math.exp(-2*beta*m)))
    return dict(distinct_split_labels=len(labels),bounds=trial,microcanonical=thermal)


def radiation_channels():
    # Three equal quadrupoles at 120 degrees. Test with actual TT projections on 4D null directions.
    axis=np.array([[math.cos(2*math.pi*j/3),math.sin(2*math.pi*j/3),0.] for j in range(3)])
    tensors=np.array([np.outer(a,a)-np.eye(3)/3 for a in axis])
    gram=np.zeros((3,3))
    nodes,weights=np.polynomial.legendre.leggauss(12)
    for z,w in zip(nodes,weights):
        for phi in np.arange(30)*2*math.pi/30:
            normal=np.array([math.sqrt(1-z*z)*math.cos(phi),math.sqrt(1-z*z)*math.sin(phi),z])
            P=np.eye(3)-np.outer(normal,normal)
            trans=np.array([P@Q@P-P*np.trace(P@Q)/2 for Q in tensors])
            gram+=w*np.einsum("iab,jab->ij",trans,trans)
    gram/=gram[0,0]
    assert np.max(abs(gram-(np.eye(3)*9/8-np.ones((3,3))/8)))<1e-12
    code=np.array([[1.,1.],[-1.,1.],[0.,-2.]])/np.sqrt([2,6])[None,:]
    assert np.linalg.norm(code.T@gram@code-(9/8)*np.eye(2))<1e-12
    # Directly monitor three common partition operators. The single-minority sector is a physical code.
    _,_,V,d3,d5=matrices(2)
    ops=[V,np.diag(d3),np.diag(d5)]
    ident=np.eye(2)
    lift=lambda a: np.kron(np.kron(a,ident),ident)+np.kron(np.kron(ident,a),ident)+np.kron(np.kron(ident,ident),a)
    rng=np.random.default_rng(128)
    states=np.eye(8)[:,[4,2,1]]@code
    history=[]
    for j in range(6):
        op=lift(ops[j%3])
        w,U=eigh(op)
        sample=rng.standard_normal()
        M=(U*np.exp(-.4*(w-sample)**2)[None,:])@U.T
        history.append(M if j%2==0 else M@history[-1])
    err=0.
    for h in history:
        for g in history:
            compressed=states.T@h.T@g@states
            err=max(err,float(np.linalg.norm(compressed-np.eye(2)*np.trace(compressed)/2)))
    assert err<1e-12
    losses=[]
    for n in (1,2,3,4):
        states_n,counts_n,V,d3,d5=matrices(n)
        dim=len(states_n)
        I=np.eye(dim)
        norm=max(1.,max(abs(np.linalg.eigvalsh(V))))
        monitor=[V/norm,np.diag(d3),np.diag(d5)]
        generator=sum(dephasing_cost(O) for D in monitor for O in (np.kron(D,I),np.kron(I,D)))
        number=np.outer(counts_n[:,0],counts_n[:,0]).ravel()
        gen_diag=(number[:,None]+number[None,:]).ravel()/2
        generator[np.diag_indices(len(gen_diag))]+=gen_diag
        loss=float(eigh(generator,subset_by_index=[0,0],eigvals_only=True)[0])
        assert loss>1e-8
        losses.append(dict(level=n,pair_dimension=dim*dim,slowest_no_emission_rate=loss))
    C=8/9
    z=math.sqrt(1-C)
    n=6400
    K=232
    f=K/(2*n)
    alpha=1e-4
    target_Kf=48*C**2*z*z
    return dict(angular_gram=gram.tolist(),angular_widths=np.linalg.eigvalsh(gram).tolist(),
                record_compression_error=err,pair_loss=losses,clock=dict(level=n,cover=K,rim_fraction=f,
                 required_cover_times_fraction=target_Kf,actual_beta_over_Hawking=math.sqrt(K*f/target_Kf),
                 time_per_cycle_over_available_at_matched_temperature=384*math.pi*alpha,
                 example_hawking_power_coefficient=alpha))


def material_loading():
    # Loading from one short charge. Pair annihilation removes one unit (in each chirality).
    # Energy never enters from a classical drive in this resonant rotating-wave model.
    data=[]
    for n in (1,2,3):
        states,occ,V,d3,d5=matrices(n)
        d=len(states)
        size=d*d+1
        hard=states.index((n,))
        H=np.zeros((size,size))
        H[0,1+hard*d+hard]=H[1+hard*d+hard,0]=.4
        I=np.eye(d)
        length=max(1.,max(abs(np.linalg.eigvalsh(V))))
        loss=np.zeros((size*size,size*size),complex)
        for O in (V/length,np.diag(d3),np.diag(d5)):
            for op in (np.kron(I,O),np.kron(O,I)):
                obs=np.zeros((size,size))
                obs[1:,1:]=op
                loss+=dephasing_cost(obs)
        loss+=1j*(np.kron(H,np.eye(size))-np.kron(np.eye(size),H.T))
        num=np.r_[0.,np.outer(occ[:,0],occ[:,0]).ravel()]
        loss[np.diag_indices(size**2)]+=(num[:,None]+num[None,:]).ravel()/2
        lowest=float(np.linalg.eigvals(loss).real.min())
        assert lowest>1e-8
        data.append(dict(level=n,loading_matrix_element=.4,smallest_decay_exponent=lowest))
    from scipy.linalg import expm
    times=[]
    for t in (4.,10.,20.):
        mat=np.array([[0.,-.25j],[-.25j,-.5]])
        state=expm(t*mat)@np.array([1.,0.],complex)
        predicted=math.exp(-t/2)*((1+t/4)**2+(t/4)**2)
        check(float(np.vdot(state,state).real),predicted)
        times.append(dict(time_in_inverse_width=t,survival=predicted,
                          tagged_qubit_entanglement_fidelity=1-3*predicted/4))
    return dict(levels=data,critical_coupling=times)


def correlated_emission():
    """Follow which energy can escape when initial thermal marginals have definite partners."""
    counts = partition_counts(6400)
    cases = []
    for level in (8, 100, 400, 1600, 6400):
        common_energy = 0.
        for mode in range(1, level+1):
            tail = (counts[level-r*mode]/counts[level] for r in range(1,level//mode+1))
            common_energy += mode*sum(prob**2 for prob in tail)
        if level==8:
            states = list(partitions(level))
            occ = np.array([[word.count(j) for j in range(1,level+1)] for word in states])
            brute = np.minimum(occ[:,None,:],occ[None,:,:])@np.arange(1,level+1)
            check(common_energy,float(brute.mean()))
            no_common = [1]
            for n in range(1, level+1):
                no_common.append(counts[n]**2-sum(counts[k]*no_common[n-k] for k in range(1,n+1)))
            for k in range(level+1):
                assert np.count_nonzero(brute==k)==counts[k]*no_common[level-k]
        j = max(1,round(.43*math.sqrt(level)))
        n2 = sum((2*r-1)*counts[level-r*j]/counts[level] for r in range(1,level//j+1))
        reverse = 1+sum((2*r+1)*counts[level-j-r*j]/counts[level-j] for r in range(1,(level-j)//j+1))
        charge_ratio = counts[level-j]/counts[level]
        check(n2/reverse,charge_ratio)
        cases.append(dict(level=level,mode=j,partner_emission_over_lower_reverse=n2/reverse,
                          independent_emission_over_lower_reverse=charge_ratio**2,
                          complete_release_probability=1/counts[level],remaining_fraction_after_release=1-common_energy/level))
    epsilon = 2/297
    x = .5
    ratio = (x**2+epsilon*x*(1+x))/(1+epsilon*(1+x))
    check(ratio/x**2,1.01)
    last_clock = math.log(100)/epsilon
    check(math.exp(-epsilon*last_clock),.01)
    return dict(finite_level=cases,limiting_unmixed_fraction=.75,
                allowed_partner_width=epsilon,terminal_time_in_ordinary_inverse_widths=last_clock)


def passive_boundary_response():
    """Retarded input for a massive scalar, the reflected signal and a finite delay."""
    from scipy.special import j1
    disk = []
    for mass in (0., .4, 3.):
        for laplace in (.3, 1., 2.):
            decay = math.hypot(laplace,mass)
            def integrand(p):
                if mass==0:
                    return laplace**2/(p*p+decay**2)
                return laplace**2*p**2/((p*p+mass**2)*(p*p+decay**2))
            continuum = mass+2/math.pi*quad(integrand,0,np.inf,epsabs=1e-12)[0]
            check(continuum,decay)
            L = 1.4
            momenta = np.arange(1,40001)*math.pi/L
            levels = mass**2+momenta**2
            base = mass/math.tanh(mass*L) if mass else 1/L
            estimate = base+2/L*np.sum(momenta**2*laplace**2/(levels*(levels+laplace**2)))
            exact = decay/math.tanh(decay*L)
            remainder = 2*L*laplace**2/(math.pi**2*len(momenta))
            assert 0<exact-estimate<=remainder*(1+1e-7)
            ratio = (decay-exact)/(decay+exact)
            check(ratio,-math.exp(-2*decay*L))
            trip = 2*L
            # Fourier-Bessel echo tail in real time, checked against its Laplace transform.
            def tail(t):
                distance = math.sqrt(max(0., t*t-trip**2))
                profile = mass/2 if distance==0 else j1(mass*distance)/distance
                return trip*mass*profile*math.exp(-laplace*t)
            echo = -math.exp(-laplace*trip)+quad(tail,trip,np.inf,epsabs=4e-13,limit=350)[0]
            check(echo,ratio)
            disk.append(dict(threshold=mass,laplace=laplace,semi_infinite_response=continuum,
                             finite_response=exact,finite_sum_error=exact-estimate,
                             guaranteed_tail_bound=remainder,reflected_laplace=echo))
    return dict(samples=disk,minimum_delay_length_m_for_full_window=299792458.*16.49e-6/2)


def passive_material_tide():
    """Two resonant sets of planar stretch modes coupled only by their Newtonian tide."""
    newton = 6.67430e-11
    hbar = 1.054571817e-34
    light = 299792458.
    proper_margin = 16.49e-6
    omega = 1e6
    axis = np.array([0., 0., 1.])
    identity = np.eye(3)
    directions = [np.array([math.cos(phi), math.sin(phi), 0.]) for phi in (0., 2*math.pi/3, 4*math.pi/3)]
    tensors = [np.outer(unit, unit)-identity/3 for unit in directions]
    # Evaluate the fourth spatial derivative at unit radius before contracting the two STF tensors.
    from itertools import combinations as select_pairs
    fourth = np.empty((3,3,3,3))
    for indices in np.ndindex(fourth.shape):
        base = 105*math.prod(axis[i] for i in indices)
        for pair in select_pairs(range(4), 2):
            x, y = (indices[p] for p in pair)
            base -= 15*identity[x,y]*math.prod(axis[indices[p]] for p in range(4) if p not in pair)
        for i,j,k,l in ((0,1,2,3),(0,2,1,3),(0,3,1,2)):
            base += 3*identity[indices[i],indices[j]]*identity[indices[k],indices[l]]
        fourth[indices] = base
    kernels = np.array([[np.einsum("ij,ijkl,kl",one,fourth,two) for two in tensors] for one in tensors])
    assert np.allclose(kernels,4.5*(np.eye(3)+np.ones((3,3))))
    rates = []
    for mass, length in ((70., .1),(1.31e-9, 1e-5)):
        # The mass of each body is assigned to three equal dumbbells.
        reduced = mass/12
        distance = 10*length
        matrix_element = 2*reduced*length*math.sqrt(hbar/(2*reduced*omega))
        frequency = (np.linalg.eigvalsh(kernels)[0]/4)*newton*matrix_element**2/(hbar*distance**5)
        independent = 9*newton*reduced*length**2/(4*omega*distance**5)
        check(frequency/independent,1)
        assert omega*distance/light < .01
        rates.append(dict(mass_kg=mass,length_m=length,separation_m=distance,
                          logical_frequency_per_second=frequency,transfer_before_horizon=math.sin(frequency*proper_margin)**2,
                          earliest_perfect_exchange_seconds=math.pi/(2*frequency)))
    return dict(kernel=kernels.tolist(),proper_window_s=proper_margin,proper_frequency_rad_s=omega,
                required_logical_frequency_per_second=math.pi/(2*proper_margin),examples=rates)


def terminal_geometry():
    # Constant proper radial speed, flat reference, p=sigma/2, outgoing null flux.
    branches=[]
    for a in (1.,2.,3.,5.):
        s=1/math.sqrt((a+2)**2-1)
        B=math.sqrt(1+s*s)
        qstar=2*(B-2*s)/3
        def rad_data(x):
            q=qstar*x**a/(1+x**a)
            compact=2*B*q-q*q
            z=B-s-q
            k=x*x*q
            kprime=2*x*q+x*a*q/(1+x**a)
            return q,k,compact,z,kprime
        # Use the first-order dynamical system independently of its logistic solution.
        start=1.2
        fin=.22
        q0,k0,c0,z0,_=rad_data(start)
        def rhs(t,state):
            x,v,k,m,u=state
            b=math.sqrt(1+v*v)
            z=b-k/x**2+v
            dk=-s*rad_data(x)[4]
            return [v,b*(dk/k+b/x-1.5*k/x**3),dk,dk*z/x,1/z]
        sol=solve_ivp(rhs,[0,(start-fin)/s],[start,-s,k0,start*c0/2,0],
                      rtol=1e-12,atol=2e-14,t_eval=np.linspace(0,(start-fin)/s,61),method="DOP853")
        assert sol.success
        # Contracting fixed-speed branches are sensitive to the initial velocity.
        x,v,k,m,u=sol.y
        expected=np.array([rad_data(w) for w in x])
        error=float(max(np.max(abs(v+s)),np.max(abs(k-expected[:,1])),np.max(abs(m-x*expected[:,2]/2))))
        assert error<5e-5,(a,error)
        initial_mass=start*c0/2
        # Integrate local radiated rest energy with the causal redshift to get Bondi mass.
        emitted=quad(lambda w:rad_data(w)[3]*rad_data(w)[4]/w if w else 0.,0,start)[0]
        check(emitted,initial_mass)
        curv=[12*rad_data(w)[2]**2/w**4 for w in (.1,.01,.001)]
        branches.append(dict(power=a,speed=s,q_at_large_radius=qstar,
                             terminal_retarded_time_over_L=quad(lambda w:1/(s*rad_data(w)[3]),0,start)[0],
                             initial_mass_over_L=initial_mass,integrated_mass_over_L=emitted,
                             curvature_in_L_units=curv,ode_max_error=error))
    return branches


def flash_bounce():
    s=1/math.sqrt(24)
    B=5*s
    L=1e6           # In Planck lengths. a=3, and qstar=2s.
    def q(r): return 2*s*(r/L)**3/(1+(r/L)**3)
    out=[]
    for k in (1.,100.,1e6):
        d=brentq(lambda r:r**2*q(r)-k,1.,L)
        m=d*(B*q(d)-q(d)**2/2)
        # The number k/G is the sum of individual angular momentum magnitudes in units of hbar.
        H=lambda r:m*r/k+k/(2*r*r)
        extremum=(k*k/m)**(1/3)
        turn=brentq(lambda r:H(r)-1,extremum,d)
        check(H(turn),1)
        compact=2*m/turn
        assert compact<8/9 and turn>2*m and extremum<turn<d
        # t=sqrt(r/Rb-1) removes the turning point from the retarded travel time.
        der=m/k-k/turn**3
        def integrand(t, sign):
            r=turn*(1+t*t)
            delta=(r-turn)*(m/k-k*(r+turn)/(2*r*r*turn*turn))
            if t==0 or delta<=0:
                return math.sqrt(2*turn/der)/(1-k/turn**2)
            speed=math.sqrt(delta*(2+delta))
            z=1+delta-k/r**2+sign*speed
            return 2*turn*t/(speed*z)
        tstart=math.sqrt(d/turn-1)
        flight=quad(lambda t:integrand(t,-1),0,tstart)[0]+quad(lambda t:integrand(t,1),0,np.inf)[0]
        # Uniform stream of tangential particles is compared to the corresponding flat-spacetime result.
        out.append(dict(angular_budget_in_hbar=k,conversion_radius=d,terminal_mass=m,bounce_radius=turn,
                        compactness_at_turn=compact,retarded_flight_in_planck_lengths=flight,
                        terminal_curvature=48*m*m/d**6,local_max_photon_count_if_each_J_at_least_one=k))
    return out


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,default=ROOT/"verification"/"soft-charge-release-results.json")
    out=parser.parse_args().output
    result=dict(reversible=reversible(),irreversible=irreversible(),counting=counting(),
                regular=terminal_geometry(),bounce=flash_bounce(),channels=radiation_channels(),loading=material_loading(),input_tide=passive_material_tide(),capture_response=passive_boundary_response(),
                partner_emission=correlated_emission())
    out.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf-8")
    print(out.name)
