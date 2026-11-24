"""Einstein--Maxwell transmission and finite-energy relational pair sources."""
from functools import lru_cache
from itertools import permutations
from math import comb, exp, expm1, log, sqrt

import numpy as np
from scipy.integrate import quad as integrate_scalar, solve_ivp
from scipy.optimize import brentq
from scipy.special import roots_legendre


@lru_cache(None)
def axial_mode(x, charge, ell, mode, outer_phase, order):
    # 2M=1, Q=charge/2, x=2M omega. Both ends use this one tortoise origin.
    Q=charge/2
    delta=sqrt(1-charge**2)
    rp,rm=(1+delta)/2,(1-delta)/2
    L=ell*(ell+1)
    q=1.5+mode*sqrt(2.25+4*Q*Q*(L-2))
    def star(r):
        return r+(rp*rp*log(r-rp)-rm*rm*log(r-rm))/delta
    def coeff(r):
        return L/r**2-q/r**3+4*Q*Q/r**4
    h=1e-7
    start=rp+h
    f=(1-rp/start)*(1-rm/start)
    slope=coeff(rp)/(delta/rp**2-2j*x)
    phase=np.exp(-1j*x*star(start))
    wave=phase*(1+slope*h)
    def field(y,vec):
        r=rp+exp(y)
        potential=(1-rp/r)*(1-rm/r)*coeff(r)
        jac=r*r/(r-rm)
        return jac*vec[1],jac*(potential-x*x)*vec[0]
    end=outer_phase/x
    sol=solve_ivp(field,(log(h),log(end-rp)),[wave,-1j*x*wave+f*phase*slope],
                  method="DOP853",rtol=1.5e-11,atol=1.5e-13)
    assert sol.success
    series=[1.+0j]
    for n in range(1,order+1):
        v=(n*(n-1)-L)*series[-1]
        if n>=2:
            v+=(q-n*(n-2))*series[-2]
        if n>=3:
            v+=Q*Q*(n*(n-3)-4)*series[-3]
        series.append(v/(2j*x*n))
    terms=np.array([c/end**n for n,c in enumerate(series)])
    phase=np.exp(1j*x*star(end))
    outgoing=phase*terms.sum()
    derivative=1j*x*outgoing-phase*(1-rp/end)*(1-rm/end)/end*np.dot(np.arange(len(terms)),terms)
    incoming,reflected=np.linalg.solve([[outgoing.conjugate(),outgoing],[derivative.conjugate(),derivative]],sol.y[:,-1])
    t,r=1/incoming,reflected/incoming
    assert abs(abs(t)**2+abs(r)**2-1)<3e-9
    return t


def transport(x,charge,outer=48.,order=9):
    ell=2
    # The source-side g,e axes are the same real flux-normalized master basis
    # continued to the up port. A local material emitter must actually excite it.
    Q=charge/2
    angle=.5*np.arctan2(2*Q*sqrt(ell*(ell+1)-2),1.5)
    c,s=np.cos(angle),np.sin(angle)
    U=np.array([[c,-s],[s,c]])
    t=np.array([axial_mode(x,charge,ell,j,outer,order) for j in [-1,1]])
    T=U@np.diag(t)@U.T
    delta=sqrt(1-charge**2)
    nh=1/expm1(4*np.pi*x*((1+delta)/2)**2/delta)
    K=nh*(T@T.conj().T)
    A,B=K[0,0].real,K[1,1].real
    v=abs(K[0,1])**2/(A*B)
    q=10*nh**2*abs(t[0]*t[1])**2
    assert abs(q-10*(A*B-abs(K[0,1])**2))<1e-12*max(1e-25,q)
    eta=abs(T[0,1])**2
    noise=nh*abs(T[0,0])**2
    return dict(x=x,Q_over_M=charge,transmissions=list(abs(t)**2),species_conversion=eta,
                thermal_noise=noise,visibility_squared=v,angular_mismatch=2*(1-v)/(5+v),
                occupation_per_up_mode=nh,antisymmetric_pairs_per_mode=q)


def observer_selection(K, angular=5):
    """Two earlier receipts and two later receipts, conditioned on all four arrivals."""
    terms=np.zeros(4,dtype=complex)
    swaps=[[0,1,2,3],[1,0,2,3],[0,1,3,2],[1,0,3,2]]
    for p in permutations(range(4)):
        prod=np.prod([K[i,p[i]] for i in range(4)])
        for index,s in enumerate(swaps):
            comp=[s[p[j]] for j in range(4)]
            unseen=set(range(4))
            cycles=0
            while unseen:
                j=next(iter(unseen))
                cycles+=1
                while j in unseen:
                    unseen.remove(j)
                    j=comp[j]
            terms[index]+=prod*angular**cycles
    assert np.max(abs(terms.imag))<2e-12*terms[0].real
    Z,X,Y,V=terms.real/terms[0].real
    held=(1+X)/2
    unbiased=(1-Y)/2
    later_held=(1+X-Y-V)/(2*(1+X))
    later_lost=(1-X-Y+V)/(2*(1-X))
    assert abs(held*later_held+(1-held)*later_lost-unbiased)<1e-12
    return [held,unbiased,later_held,later_lost]


def charged_results():
    rows=[transport(x,c) for c in [0.,.2,.6,.9] for x in [.1,.25,.5,.7,1.]]
    for c,x in [(.2,.25),(.6,.7),(.9,1.)]:
        old=next(r for r in rows if r["x"]==x and r["Q_over_M"]==c)
        new=transport(x,c,70.,12)
        for key in ["species_conversion","thermal_noise","angular_mismatch"]:
            assert abs(old[key]-new[key])<3e-9
    crossings=[]
    for c in [.2,.6,.9]:
        def criterion(x):
            t=transport(x,c)
            return t["species_conversion"]-t["thermal_noise"]
        # Record a sign change, with the bracket. Further passbands are allowed.
        grid=np.geomspace(.01,1.,20)
        for l,r in zip(grid,grid[1:]):
            if criterion(l)*criterion(r) < 0:
                root=brentq(criterion,l,r,xtol=2e-10)
                crossings.append([c,float(l),float(r),root])
                break
    def count(nodes):
        xs,ws=roots_legendre(nodes)
        xs=(xs+1)*1.2
        ws=ws*1.2/(2*np.pi)
        values=[transport(float(x),.6) for x in xs]
        density=np.array([r["occupation_per_up_mode"]*np.array(r["transmissions"]) for r in values])
        I=ws@density
        angle=.5*np.arctan2(1.2,1.5)
        c,s=np.cos(angle),np.sin(angle)
        ee,gg=c*c*I[0]+s*s*I[1],s*s*I[0]+c*c*I[1]
        ret=[]
        for dt in [0.,1.,4.,10.,30.]:
            eg=np.dot(ws*np.exp(-1j*xs*dt),c*s*(density[:,0]-density[:,1]))
            v=abs(eg)**2/(ee*gg)
            ret.append([dt,10*(ee*gg-abs(eg)**2),2*(1-v)/(5+v)])
        assert abs(ret[0][1]-10*I.prod())<1e-22
        histories=[]
        U=np.array([[c,-s],[s,c]])
        for dt in [0.,1.,4.,10.,30.]:
            times=np.array([0.,0.,dt,dt])
            K=np.zeros((4,4),complex)
            for i in range(4):
                for j in range(4):
                    e=ws*np.exp(-1j*xs*(times[i]-times[j]))
                    K[i,j]=np.dot(U[i%2]*U[j%2],e@density)
            histories.append([dt,*observer_selection(K)])
        def mismatch_gap(dt):
            cross=np.dot(ws*np.exp(-1j*xs*dt),c*s*(density[:,0]-density[:,1]))
            return abs(cross)**2/(ee*gg)-7/13
        return I,ret,brentq(mismatch_gap,0.,4.),histories
    first,rough,ct0,hh0=count(52)
    final,schedules,ct,hh=count(76)
    assert np.max(abs(np.array(hh)-np.array(hh0)))<3e-5
    assert abs(ct0-ct)<1e-4
    assert np.max(abs(first-final))<2e-11
    critical=[(sqrt(1393)-17)/46,9/20,2*sqrt(3)-3]
    contrast=[]
    for v in critical:
        charge=brentq(lambda z: transport(.7,z)["visibility_squared"]-v,0.,.6)
        K=np.array([[1. if i%2==j%2 else sqrt(v) for i in range(4)] for j in range(4)])
        contrast.append([v,charge,*observer_selection(K)])
    return dict(odd_j2=rows,crossings=crossings,survival_contrast=contrast,broadband_Q_point6_integrals=list(final),
                broadband_equal_time_limit=10*final.prod(),broadband_delays=schedules,
                broadband_first_thickness_crossing=ct,observer_selection=hh,capacity=capacity_results())


def capacity_results():
    """Unassisted two-eigenchannel quantum capacity at the Hawking input mean."""
    def entropy(n):
        if n <= 0:
            return 0.
        return np.log1p(n)+n*np.log1p(1/n)
    rows=[]
    for charge in (0.,.6,.9):
        delta=sqrt(1-charge**2)
        beta=4*np.pi*((1+delta)/2)**2/delta
        modes=[]
        for mode in [-1,1]:
            def tau(x):
                return min(1.,abs(axial_mode(float(x),charge,2,mode,48.,9))**2)
            crossing=brentq(lambda x:tau(x)-.5,.4,1.6,xtol=5e-11)
            def compute(npts):
                nodes,weights=roots_legendre(npts)
                result=np.zeros(2)
                for lo,hi in [(0.,crossing),(crossing,3.)]:
                    for x,weight in zip((hi+lo+(hi-lo)*nodes)/2,weights*(hi-lo)/2):
                        eta=tau(x)
                        n=1/expm1(beta*x)
                        result+=weight*np.array([max(0.,entropy(eta*n)-entropy((1-eta)*n)),beta*x*eta*n])
                return result
            coarse=compute(24)
            final=compute(36)
            assert np.max(abs(coarse-final)) < 2e-10
            modes.append([mode,crossing,*final])
        Qcap=sum(k[2] for k in modes)
        heat=sum(k[3] for k in modes)
        rows.append(dict(Q_over_M=charge,modes=modes,capacity_per_area_entropy=Qcap/heat))
    return rows


def soft_absorption():
    """Leading soft gravitational exponent, B/(G E^2), for a resolved neutral recoil."""
    def analytic(e):
        # Integral over z=(cos theta). Long wavelength and TT norm epsilon*:epsilon=1.
        direct=integrate_scalar(lambda z:(1+z)**2/(1+e*(1-z))**2,-1.,1.)[0]
        closed=((1+2*e)**2-1-2*(1+2*e)*np.log1p(2*e))/e**3
        assert abs(direct-closed)<1e-10
        return direct/(2*np.pi)
    def sky(angle,e,order):
        nodes,ws=roots_legendre(order)
        split=np.cos(angle/2)
        intervals=[(-1.,split)] + ([(split,1.)] if split<1. else [])
        cosines=np.concatenate([((a+b)+(b-a)*nodes)/2 for a,b in intervals])
        weights=np.concatenate([ws*(b-a)/2 for a,b in intervals])
        azimuth=(np.arange(2*order)+.5)*np.pi/order
        z=cosines[:,None]
        st=np.sqrt(1-z*z)
        cp,sp=np.cos(azimuth),np.sin(azimuth)
        # Divide all hard momenta by total incoming energy E.
        dz=np.cos(angle/2)
        def current(px,pz,energy):
            along=px*st*cp+pz*z
            t=px*z*cp-pz*st
            p=-px*sp
            den=energy-along
            return np.stack([(t*t-p*p)/den,np.broadcast_to(2*t*p/den,t.shape)])/sqrt(2)
        src=current(0.,dz,1+1/e)-current(np.sin(angle/2)/2,dz/2,.5)-current(-np.sin(angle/2)/2,dz/2,.5)
        return np.sum(weights[:,None]*np.sum(src**2,axis=0))*(np.pi/order)/(2*np.pi**2)
    data=[]
    for e in [.05,.2,1.]:
        full=analytic(e)
        assert abs(sky(0.,e,48)-full)<3e-13
        data.append([e,full])
    pairs=[[a,sky(a,.2,180),sky(a,.2,320)] for a in [.2,.1,.05,0.]]
    assert all(abs(row[1]-row[2])<3e-7 for row in pairs)
    return dict(single_source_exponent_over_GE2=data,two_photon_opening_radians=pairs,
                heavy_absorber_limit=4/(3*np.pi))


def matrix_currents():
    # Bosonic BFSS, traceless 3x3 blocks. Gauss vanishes on this invariant ansatz.
    def ode(t,state):
        y,d,p,v=state
        return [p,v,-4*y*(y*y+d*d),-8*y*y*d]
    sol=solve_ivp(ode,(0.,2.),[1.,.5,0.,0.],rtol=2e-13,atol=2e-15,
                  t_eval=[0,.1,.4,.8,1.5,2.],method="DOP853")
    assert sol.success
    y,d,v,w=sol.y
    H=2*v*v+w*w+4*y**4+8*y*y*d*d
    assert max(abs(H-H[0]))<5e-11
    c=.5
    q=2*(6*c*c+2*d*d)/3
    j=16*c*d*y*y/3
    # Check the traces independently on actual matrices.
    for a,b,Q,J in zip(y,d,q,j):
        X=np.diag([c+b,c-b,-2*c])
        Y=np.array([[0,a,0],[a,0,0],[0,0,0]])
        Z=np.array([[0,-1j*a,0],[1j*a,0,0],[0,0,0]])
        assert abs((2/3)*np.trace(X@X)-Q)<1e-14
        assert abs((-2j/3)*np.trace(X@X@(Y@Z-Z@Y))-J)<1e-14
    return dict(t=list(sol.t),mass_quadrupole=list(q),membrane_quadrupole=list(j),
                energy_drift=float(max(abs(H-H[0]))),derivative_minor=-1280)



def primitive_source(m=5):
    # Gaussian action on a rooted multigraph: one pin per site, four mutual edges.
    stiffness=np.array([[5.,-4.],[-4.,5.]])
    freq=np.sqrt(np.linalg.eigvalsh(stiffness))
    omega=sqrt(np.prod(freq))
    lam=(sqrt(freq[1])-sqrt(freq[0]))/(sqrt(freq[1])+sqrt(freq[0]))
    assert abs(lam-(2-sqrt(3)))<1e-15
    U=np.array([[-3.,4.],[4.,3.]])/5
    T=U@np.diag([1.,2/3])@U.T
    finite=[]
    for L in [1,2,4,8,16]:
        D=np.array([comb(N+m-1,m-1) for N in range(L+1)])
        amp=lam**np.arange(L+1)*np.sqrt(D)
        amp/=np.linalg.norm(amp)
        difference=np.zeros((L,L+1))
        for N in range(L):
            difference[N,N]=-lam*sqrt((N+m)/(N+1))
            difference[N,N+1]=1
        parent=difference.T@difference
        ev=np.linalg.eigvalsh(parent)
        assert np.linalg.norm(parent@amp)<1e-15 and ev[1]>0.1
        occ=np.dot(amp**2,np.arange(L+1))/m
        rate=m*(m-1)/2*occ**2*abs(np.linalg.det(T))**2
        finite.append([L,occ,rate,ev[1]])
    # A returned auxiliary and a direct phase agree for all inputs at completion.
    I=np.eye(2)
    X=np.array([[0,1],[1,0]])
    Z=np.diag([1,-1])
    for a in [0,1]:
        for b in [0,1]:
            A=X if a else I
            B=Z if b else I
            assert np.array_equal(A@B@A@B,(-1)**(a*b)*I)
    return dict(mode_frequencies=list(freq),receiver_frequency=omega,squeeze_amplitude=lam,
                unlimited_occupation=lam**2/(1-lam**2),two_site_quench_energy_variance=(freq[1]-freq[0])**2/4,
                squared_transmission_determinant=abs(np.linalg.det(T))**2,finite_sources=finite)
