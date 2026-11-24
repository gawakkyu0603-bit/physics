"""The ordinary CAT commutator on two oscillator number spaces and its compact scale."""
from functools import lru_cache
import json
import math
import os
from pathlib import Path

# The rank-five Hessian performs many small, independent matrix products.
os.environ["OPENBLAS_NUM_THREADS"]="1"
os.environ["OMP_NUM_THREADS"]="1"
import numpy as np
from scipy.linalg import eigh, null_space
from scipy.integrate import quad
from scipy.special import xlogy
from scipy.optimize import minimize, minimize_scalar


@lru_cache(None)
def states(n):
    return tuple((a,b,c,n-a-b-c) for a in range(n+1)
                 for b in range(n-a+1) for c in range(n-a-b+1))


@lru_cache(None)
def annihilators(n):
    indices={s:i for i,s in enumerate(states(n-1))}
    links=np.zeros((4,len(indices),len(states(n))))
    for col,occ in enumerate(states(n)):
        for axis,occupation in enumerate(occ):
            if occupation:
                lower=list(occ)
                lower[axis]-=1
                links[axis,indices[tuple(lower)],col]=math.sqrt(occupation)
    return links


def matrices(links):
    low,high=links.shape[1:]
    result=np.zeros((4,high+low,high+low))
    result[:,:high,high:]=links.transpose(0,2,1)
    result[:,high:,:high]=links
    return result


def left_minus_right(left,right):
    # Column-wise vectorization of a rectangular matrix.
    return np.kron(np.eye(len(right)),left)-np.kron(right.T,np.eye(len(left)))


def rep_dim(a,b,c):
    return (a+1)*(b+1)*(c+1)*(a+b+2)*(b+c+2)*(a+b+c+3)//12


def even_roots(n,h,ell):
    total=2*n+h+3
    degree=2*ell+h
    determinant=degree*(degree+6)/4
    high=(total+math.sqrt(total**2-4*determinant))/2
    return determinant/high,high


def check_spectrum(n,h):
    right,left=matrices(annihilators(n)),matrices(annihilators(n+h))
    pairs=[left_minus_right(l,r) for l,r in zip(left,right)]
    lap=sum(p@p for p in pairs)/2
    parity_l=np.r_[np.ones(len(states(n+h))),-np.ones(len(states(n+h-1)))]
    parity_r=np.r_[np.ones(len(states(n))),-np.ones(len(states(n-1)))]
    parity=np.kron(parity_r,parity_l)
    even=lap[np.ix_(parity>0,parity>0)]
    odd=lap[np.ix_(parity<0,parity<0)]
    assert np.max(abs(lap[np.ix_(parity>0,parity<0)]))==0.
    levels=[]
    for ell in range(n+1):
        lo,hi=even_roots(n,h,ell)
        levels.extend([lo]*rep_dim(ell+h,0,ell))
        if ell<n:
            levels.extend([hi]*rep_dim(ell+h,0,ell))
    np.testing.assert_allclose(eigh(even,eigvals_only=True),np.sort(levels),atol=2e-12)
    # The two odd rectangles have different sizes for h>0. The unmatched
    # states sit exactly at the midpoint. The paired states are ladders in
    # the two oscillator species with fixed total number.
    mid=(2*n+h+3)/2
    odd_levels=[]
    for j in range(n):
        singular=math.sqrt((n-j)*(n+h-j))
        multiplicity=rep_dim(2*n+h-1-2*j,j,0)
        odd_levels.extend([mid-singular]*multiplicity)
        odd_levels.extend([mid+singular]*multiplicity)
    odd_levels += [mid]*(len(odd)-len(odd_levels))
    np.testing.assert_allclose(eigh(odd,eigvals_only=True),np.sort(odd_levels),atol=3e-12)
    return dict(level=n,charge=h,even_states=len(even),odd_states=len(odd),
                lowest_odd=min(odd_levels),first_even=even_roots(n,h,int(h==0))[0])


def bounded_linear_embedding():
    eye=np.eye(4)
    axes=[]
    for i in range(4):
        for j in range(i+1,4):
            axes.append((np.outer(eye[i],eye[j])-np.outer(eye[j],eye[i]))/(2j))
    generators=axes.copy()
    for i in range(4):
        for j in range(i+1,4):
            generators.append((np.outer(eye[i],eye[j])+np.outer(eye[j],eye[i]))/2)
    for i in range(1,4):
        generators.append(np.diag([1]*i+[-i]+[0]*(3-i))/math.sqrt(2*i*(i+1)))
    generators=np.array(generators)
    adj=np.array([[2*np.einsum('ij,aji->a',x@y-y@x,generators)
                   for y in generators] for x in generators])
    image=[]
    for i in range(15):
        for j in range(i,15):
            product=adj[i]@adj[j]
            if i!=j:
                product=(product+adj[j]@adj[i])/math.sqrt(2)
            image.append(product.real.ravel())
    singular=np.linalg.svd(image,compute_uv=False)
    np.testing.assert_allclose(singular,np.repeat([4.,2.,1.],[1,15,104]),atol=1e-12)
    masses=eigh(sum(t@t for t in adj[:6]),eigvals_only=True)
    np.testing.assert_allclose(masses,np.repeat([1.,2.],[6,9]))
    return dict(axes=6,relative_rms=np.std(masses)/np.mean(masses),multiplicities=[6,9])


def normalized_raise(n,h):
    result=np.eye(len(states(n)))
    for step in range(1,h+1):
        result=annihilators(n+step)[0].T@result/math.sqrt(n+step)
    return result


def product_case(n,h,k):
    # Each block is normalized to have a unit coherent highest-weight symbol.
    def lower_amplitude(level,charge):
        return (level+charge/2-even_roots(level,charge,0)[0])/math.sqrt(level*(level+charge))
    top=normalized_raise(n+h,k)@normalized_raise(n,h)
    bottom=normalized_raise(n+h-1,k)@normalized_raise(n-1,h)
    np.testing.assert_allclose(top,normalized_raise(n,h+k),atol=2e-15)
    np.testing.assert_allclose(bottom,normalized_raise(n-1,h+k),atol=2e-15)
    product_ratio=lower_amplitude(n+h,k)*lower_amplitude(n,h)
    target_ratio=lower_amplitude(n,h+k)
    # Test that these block amplitudes actually give the low eigenmode.
    target_links=annihilators(n+h+k)
    source_links=annihilators(n)
    contracted=sum(l.T@bottom@r for l,r in zip(target_links,source_links))
    np.testing.assert_allclose((n+(h+k)/2)*top-target_ratio*contracted,
                               even_roots(n,h+k,0)[0]*top,atol=2e-14)
    top_norm=np.sum(top**2)
    bottom_norm=np.sum(bottom**2)
    overlap=(top_norm+product_ratio*target_ratio*bottom_norm)**2/(
        (top_norm+product_ratio**2*bottom_norm)*(top_norm+target_ratio**2*bottom_norm))
    return dict(level=n,charge_in=[h,k],charge_out=h+k,
                projected_fraction=overlap,vertex_norm_squared=top_norm+product_ratio**2*bottom_norm)


def shape_action(ys):
    # Ordered two-external/two-internal flux term. Positive eigenvalues only.
    deriv=[left_minus_right(y,y) for y in ys]
    masses,vec=eigh(sum(d@d for d in deriv))
    keep=masses>1e-9
    masses,vec=masses[keep],vec[:,keep]
    a,b=masses[:,None],masses[None,:]
    diff=b-a
    weights=np.divide(np.log1p(diff/a),diff,out=np.broadcast_to(1/a,diff.shape).copy(),
                      where=abs(diff)>1e-14*np.maximum(a,b))
    mixed,tree=0.,0.
    for i,y in enumerate(ys):
        for z in ys[i+1:]:
            flux=y@z-z@y
            tree+=np.sum(abs(flux)**2)
            vertex=vec.T.conj()@left_minus_right(flux,flux)@vec
            mixed+=np.sum(abs(vertex)**2*weights)
    return tree,mixed


def shape_cases(n):
    ys=matrices(annihilators(n))
    tree,mixed=shape_action(ys)
    def energy(mats):
        b,a=shape_action(mats)
        # In units of the tree energy at the stationary common scale.
        return b/tree-2*a/mixed
    def optimized(mats):
        b,a=shape_action(mats)
        return -(a/mixed)**2/(b/tree)
    shear=np.array([1.,-1.,0.,0.])
    def axis(s):
        return ys*np.exp(s*shear[:,None,None])
    def curvature(f,h):
        return (f(h)+f(-h)-2*f(0.))/h**2
    h=.002
    fd=[curvature(lambda s:energy(axis(s)),t) for t in (h,h/2)]
    np.testing.assert_allclose(fd[0],fd[1],rtol=1e-4,atol=1e-6)
    force=np.array([sum(z@(z@y-y@z)-(z@y-y@z)@z for z in ys) for y in ys])
    radial=np.vdot(ys,force).real/np.vdot(ys,ys).real
    transverse=force-radial*ys
    fraction=np.linalg.norm(transverse)/np.linalg.norm(force)
    row=dict(level=n,tree=tree,mixed=mixed,unit_scale_inverse_G=mixed/(2*math.pi),
             first_mode_G_mass_squared=4*math.pi*even_roots(n,0,1)[0]/mixed,
             shear_second_variation=fd[-1],tree_force_transverse_fraction=fraction)
    if fraction>1e-8:
        variation=transverse*np.linalg.norm(ys)/np.linalg.norm(transverse)
        slopes=[(optimized(ys+t*variation)-optimized(ys-t*variation))/(2*t) for t in (h,h/2)]
        np.testing.assert_allclose(slopes[0],slopes[1],rtol=5e-4)
        row["scale_minimized_transverse_slope"]=slopes[-1]
    return row


def onsite_trial(n):
    ys=matrices(annihilators(n))
    upper=len(states(n))
    parity=np.diag(np.r_[np.ones(upper),-np.ones(len(states(n-1)))])/2
    def value(mats):
        tree,mixed=shape_action(mats)
        return -mixed**2/tree
    reference=-value(ys)
    def profile(d,theta=0.,shear=0.):
        arr=ys*np.exp(shear*np.array([1.,-1.,0.,0.]))[:,None,None]
        other=1j*arr[0].copy()
        other[upper:,:upper]*=-1
        arr[0]*=np.cos(theta)
        return value([*arr,d*parity,np.sin(theta)*other])/reference
    fit=minimize_scalar(profile,bounds=(.1,7),method="bounded")
    t=.001
    def second(phase,axis,step):
        return (profile(fit.x,phase*step,axis*step)+profile(fit.x,-phase*step,-axis*step)
                -2*fit.fun)/(abs(fit.fun)*step**2)
    curv=[second(1,0,t),second(0,1,t)]
    np.testing.assert_allclose(curv,[second(1,0,2*t),second(0,1,2*t)],rtol=.0002)
    return dict(level=n,onsite=fit.x,energy_ratio=fit.fun,
                phase_curvature=curv[0],axis_curvature=curv[1])


def hermitian_basis(size):
    vec=[]
    for i in range(size):
        for j in range(i):
            z=np.zeros((size,size),complex)
            z[i,j]=z[j,i]=1/math.sqrt(2)
            vec.append(z)
            vec.append(1j*(np.tril(z)-np.triu(z)))
    for j in range(1,size):
        vec.append(np.diag([1.]*j+[-j]+[0.]*(size-j-1))/math.sqrt(j*(j+1)))
    return np.array(vec)


class CompactShape:
    """Scale-minimized tree plus ordered mixed loop on six traceless matrices."""
    def __init__(self,size,order=24):
        self.basis=hermitian_basis(size)
        self.size=size
        # Real antisymmetric matrices representing -i times the commutator.
        self.ad=np.asarray([np.einsum('aij,bji->ab',self.basis,
            -1j*(g@self.basis-self.basis@g)).real for g in self.basis])
        x,w=np.polynomial.legendre.leggauss(order)
        self.abscissa=(1+x)/(1-x)
        self.measure=2*w/(1-x)**2
        self.ix,self.jx=np.triu_indices(6,1)

    def coordinates(self,ys):
        return np.einsum('aij,kji->ka',self.basis,ys).real

    def value_gradient(self,flat):
        # The discarded identity is an exact central mode for every configuration.
        xs=flat.reshape(6,-1)
        ad=xs@self.ad.reshape(len(self.ad),-1)
        ad=ad.reshape((6,len(self.ad),len(self.ad)))
        lams,u=eigh(-np.sum(ad@ad,axis=0))
        if lams[0]<1e-9:
            raise ValueError("an additional light subalgebra needs its own matching")
        sigma=(lams[-1]*lams[0])**.5
        g=1/(lams+sigma*self.abscissa[:,None])
        weight=self.measure*sigma
        ds=u.T@ad@u
        pair=ds[self.ix]@ds[self.jx]-ds[self.jx]@ds[self.ix]
        kernel=(g.T*weight)@g
        flux_grad=2*pair*kernel
        mixed=np.sum(pair*flux_grad)/2
        # Frechet variation with respect to L and to each antisymmetric flux.
        # Sum_F F[p,q] F[r,q] first, retaining the intermediate mass index q.
        dlog=-2*np.einsum('tp,tq,tr,t->pqr',g,g,g,weight,optimize=True)
        dm=np.einsum('fpq,frq,pqr->pr',pair,pair,dlog,optimize=True)
        dx=ds@dm+dm@ds
        for i,j,h in zip(self.ix,self.jx,flux_grad):
            dx[i]+=h@ds[j].T-ds[j].T@h
            dx[j]+=ds[i].T@h-h@ds[i].T
        grad_a=(u@dx@u.T).reshape(6,-1)@self.ad.reshape(len(self.ad),-1).T
        # -i[X_i,X_j] in the orthonormal matrix basis.
        flux=(ad[self.ix]@xs[self.jx,:,None])[:,:,0]
        tree=np.sum(flux**2)
        grad_b=np.zeros_like(xs)
        for i,j,f in zip(self.ix,self.jx,flux):
            grad_b[i]+=2*(ad[j]@f)
            grad_b[j]-=2*(ad[i]@f)
        val=-mixed**2/tree
        return val,(val*(2*grad_a/mixed-grad_b/tree)).ravel()

    def hessian(self,xs,step):
        flat=xs.ravel()
        hess=np.empty((len(flat),len(flat)))
        for i,v in enumerate(np.eye(len(flat))):
            hess[i]=(self.value_gradient(flat+step*v)[1]
                     -self.value_gradient(flat-step*v)[1])/(2*step)
        return (hess+hess.T)/2

    def random_start(self,seed):
        # A fixed seed only chooses the starting point, not a term in the action.
        return np.random.default_rng(seed).normal(size=(6,len(self.basis)))


def gammas():
    pauli=[np.array([[0,1],[1,0]]),np.array([[0,-1j],[1j,0]]),np.diag([1,-1])]
    gamma=[]
    for axis in range(3):
        for pol in (0,1):
            mats=[pauli[2]]*axis+[pauli[pol]]+[np.eye(2)]*(2-axis)
            gamma.append(np.kron(np.kron(mats[0],mats[1]),mats[2]))
    return np.array(gamma)


class SummedShape(CompactShape):
    """Two external spin insertions, without expanding in internal spin."""
    def __init__(self,size):
        super().__init__(size)
        self.gamma=gammas()

    def spectrum(self,xs):
        ads=(xs@self.ad.reshape(len(self.ad),-1)).reshape(6,len(self.ad),-1)
        lap=-np.sum(ads@ads,axis=0)
        dirac=1j*np.einsum('ijk,ipq->jpkq',self.gamma,ads).reshape(8*len(self.ad),-1)
        return ads,eigh(lap),eigh(dirac)

    def value_gradient(self,flat):
        xs=flat.reshape(6,-1)
        ads,(lams,u),(d,v)=self.spectrum(xs)
        # At enhanced symmetry C_i vanishes on the kernel. The derivative of
        # x^2 log x^2 with respect to a matrix entry is continuous there.
        lams=np.maximum(lams,0.)
        mixed=2*(np.sum(xlogy(d*d,d*d))/8-np.sum(xlogy(lams,lams)))
        # The derivative at a Dirac zero is continuous.
        derivative=(xlogy(d,np.maximum(d*d,1e-300))+d)/2
        dz=(v*derivative)@v.T.conj()
        dad=np.einsum('jpkq,ikj->iqp',dz.reshape(8,len(self.ad),8,-1),1j*self.gamma).real
        dl=(u*(-2*(np.log(np.maximum(lams,1e-15*lams[-1]))+1)))@u.T
        dad+=ads@dl+dl@ads
        grad_a=dad.reshape(6,-1)@self.ad.reshape(len(self.ad),-1).T
        flux=(ads[self.ix]@xs[self.jx,:,None])[:,:,0]
        tree=np.sum(flux**2)
        grad_b=np.zeros_like(xs)
        for i,j,f in zip(self.ix,self.jx,flux):
            grad_b[i]+=2*(ads[j]@f)
            grad_b[j]-=2*(ads[i]@f)
        val=-mixed**2/tree
        return val,(val*(2*grad_a/mixed-grad_b/tree)).ravel()


def spin_test(model,xs):
    xs=xs/np.linalg.norm(xs)
    ads=np.einsum('ia,apq->ipq',xs,model.ad)
    lap=-np.sum(ads@ads,axis=0)
    masses,u=eigh(lap)
    size=len(masses)
    spin=np.array([[-2*(a@b-b@a) for b in ads] for a in ads])
    def pack(mats):
        return mats.transpose(0,2,1,3).reshape(6*size,-1)
    block=pack(spin)
    wave=block+np.kron(np.eye(6),lap)
    gauge=ads.reshape(6*size,size)
    physical=null_space(gauge.T)
    physical_masses=eigh(physical.T@wave@physical,eigvals_only=True)
    np.testing.assert_allclose(gauge.T@xs.ravel(),0.,atol=2e-14)
    np.testing.assert_allclose(block@xs.ravel(),2*(xs@lap).ravel(),atol=2e-14)
    inv=(u*masses**-.5)@u.T
    expansion=eigh(pack(inv@spin@inv),eigvals_only=True)
    return dict(first_scalar=masses[0],transverse_low=physical_masses[0],
                transverse_negative=int(np.sum(physical_masses < -1e-7)),
                required_gap_over_first_scalar=math.sqrt(max(0.,-physical_masses[0])/masses[0]),
                relative_spin_min=expansion[0],relative_spin_max=expansion[-1])


def compact_minimum(size,resummed):
    model=SummedShape(size) if resummed else CompactShape(size)
    def fit(seed):
        xs=model.random_start(seed)
        xs*=3/np.linalg.norm(xs)
        ref=-model.value_gradient(xs.ravel())[0]
        def value(z):
            v,g=model.value_gradient(z)
            return v/ref,g/ref
        direction=model.random_start(3).ravel()
        direction/=np.linalg.norm(direction)
        dt=2e-5
        z=xs.ravel()
        fd=(value(z+dt*direction)[0]-value(z-dt*direction)[0])/(2*dt)
        np.testing.assert_allclose(fd,value(z)[1]@direction,atol=8e-8)
        best=minimize(value,z,jac=True,method="L-BFGS-B",
                      options=dict(ftol=2e-15,gtol=1e-10,maxiter=210,maxls=36))
        assert np.linalg.norm(best.jac)<3e-6,(best.message,best.jac)
        return best.x.reshape(6,-1)/np.linalg.norm(best.x)
    xs=fit(1)
    second=fit(8)
    val,grad=model.value_gradient(xs.ravel())
    assert np.linalg.norm(grad)/abs(val)<4e-6
    # A Dirac zero in the summed trace gives s^2 log(s^2) on some paths.
    # It has a first derivative but need not have a finite Hessian.
    shape={}
    if not resummed:
        curvs=eigh(model.hessian(xs,.000045)/abs(val),eigvals_only=True)
        zero=np.abs(curvs)<1e-5
        shape=dict(minimum_shape_curvature=curvs[~zero][0],zero_shape_modes=int(sum(zero)))
    orbit=[xs.ravel()]
    orbit.extend((xs@a).ravel() for a in model.ad)
    for i,j in zip(model.ix,model.jx):
        rot=np.zeros_like(xs)
        rot[i],rot[j]=xs[j],-xs[i]
        orbit.append(rot.ravel())
    rank=int(np.count_nonzero(np.linalg.svd(orbit,compute_uv=False)>8e-6))
    diagnostics=spin_test(model,xs)
    ys=(xs@model.basis.reshape(len(model.basis),-1)).reshape(6,size,size)
    b,a4=shape_action(ys)
    _,(la,_),(dd,_)=SummedShape(size).spectrum(xs)
    ar=2*(np.sum(xlogy(dd**2,dd**2))/8-np.sum(xlogy(la,la)))
    np.testing.assert_allclose(-val,(ar if resummed else a4)**2/b,rtol=2e-10)
    return dict(matrix_size=size,resummed=resummed,negative_energy=-val,relative_gradient=np.linalg.norm(grad)/abs(val),
                symmetry_directions=rank,**shape,
                alternative_start_energy_ratio=model.value_gradient(second.ravel())[0]/val,
                summed_to_quartic=ar/a4,G_times_light_mass2=2*math.pi*la[0]/ar,**diagnostics)


def null_polarization(n):
    # Two real axes, two axes split into independent quadratures.
    # A compact-orbital unitary and an ambient orthogonal rotation preserve
    # all norms, so the test uses the canonical pair of real axes.
    ys=matrices(annihilators(n))
    upper=len(states(n))
    c=np.array([1.,1j,0,0])/math.sqrt(2)
    ket=np.array([math.sqrt(math.factorial(n)/math.prod(math.factorial(i) for i in occ))
                  *np.prod(c**np.array(occ)) for occ in states(n)])
    mode=np.zeros_like(ys[0],complex)
    mode[:upper,:upper]=np.outer(ket,ket)
    mats=[ys[0],ys[1]]
    for i,angle in [(2,.41),(3,.78)]:
        phase=1j*ys[i].copy()
        phase[upper:,:upper]*=-1
        mats.extend([math.cos(angle)*ys[i],math.sin(angle)*phase])
    mats=np.array(mats)
    a=np.array([mode,1j*mode,*[0*mode]*4])/math.sqrt(2)
    def comm(x,y):
        return x@y-y@x
    divergence=sum(comm(x,z) for x,z in zip(mats,a))
    lap=sum(comm(x,comm(x,a)) for x in mats)
    spin=np.array([2*sum(comm(comm(x,y),z) for y,z in zip(mats,a)) for x in mats])
    np.testing.assert_allclose(divergence,0.,atol=2e-14)
    np.testing.assert_allclose(lap,2*n*a,atol=2e-14)
    np.testing.assert_allclose(spin,-4*n*a,atol=4e-14)
    return dict(level=n,vector_mass_squared=-2*n,scalar_mass_squared=2*even_roots(n,0,1)[0],
                divergence_norm=float(np.linalg.norm(divergence)),
                required_gap_ratio=math.sqrt(n/even_roots(n,0,1)[0]))


def determinant_check():
    model=SummedShape(3)
    xs=model.random_start(17)
    xs/=np.linalg.norm(xs)
    _,(lams,_),(dirac,_)=model.spectrum(xs)
    ferm=dirac**2
    np.testing.assert_allclose(ferm.sum()/8,lams.sum(),atol=2e-13)
    entropy=lambda s: 2*(np.sum(xlogy(s*ferm,s*ferm))/8-np.sum(xlogy(s*lams,s*lams)))
    np.testing.assert_allclose(entropy(3.1),3.1*entropy(1.),rtol=1e-13)
    # Subtract 1-2m/q before summing to avoid ultraviolet loss of precision.
    def integrand(q):
        def sub(m):
            return m*m*(3*q+2*m)/(q*(q+m)**2)
        if q<1:
            return np.sum((q/(q+ferm))**2)/8-np.sum((q/(q+lams))**2)
        return np.sum(sub(ferm))/8-np.sum(sub(lams))
    integ=quad(integrand,0,1,epsabs=5e-12)[0]+quad(integrand,1,np.inf,epsabs=5e-12)[0]
    np.testing.assert_allclose(integ,entropy(1.),rtol=1e-9)
    ys=(xs@model.basis.reshape(len(model.basis),-1)).reshape(6,3,3)
    _,a4=shape_action(ys)
    ads,(lams,u),_=model.spectrum(xs)
    lap=(u*lams)@u.T
    dirac_full=1j*np.einsum('ijk,ipq->jpkq',model.gamma,ads).reshape(8*len(lams),-1)
    base=np.kron(np.eye(8),lap)
    internal=dirac_full@dirac_full-base
    def weighted(s):
        vals=eigh(base+s*internal,eigvals_only=True)
        return 2*(np.sum(xlogy(vals,vals))/8-np.sum(xlogy(lams,lams)))
    s=.003
    quadratic=(weighted(s)+weighted(-s))/(2*s*s)
    np.testing.assert_allclose(quadratic,a4,rtol=2e-5)
    return dict(momentum_integral=integ,spectral_result=entropy(1.),quartic=a4,
                weak_spin_coefficient=quadratic)


def flux_and_matter():
    def potential(u,v):
        return 18*np.exp(-21*u)-np.exp(-9*u)*(48*np.exp(2*v/7)-6*np.exp(16*v/7))
    h=2e-5
    hess=np.array([(potential(h,0)+potential(-h,0)-2*potential(0,0))/h**2,
                   (potential(0,h)+potential(0,-h)-2*potential(0,0))/h**2])
    np.testing.assert_allclose(hess,[4536,192/7],rtol=3e-6)
    masses=hess/(8*np.array([63/2,6/7]))
    np.testing.assert_allclose(masses,[18,4],rtol=3e-6)
    def mass(frac,u,v):
        return frac*np.exp(-9*u/2-6*v/7)+(1-frac)*np.exp(3*u/2+2*v/7)
    ratios=[]
    for f in (0.,.25,1.):
        d=np.array([(mass(f,h,0)-mass(f,-h,0))/(2*h),(mass(f,0,h)-mass(f,0,-h))/(2*h)])
        beta=2*np.sum(d**2/np.array([63/2,6/7]))
        np.testing.assert_allclose(beta,(4*f-1)**2/3,atol=2e-8)
        ratios.append(beta)
    eps=(1.96*2.3-2.1)*1e-5
    bound=eps/(2-eps)
    def running(t,uv,ir):
        matching=np.array([1.,2.,5.])*t
        coeff=np.array([ir,6.,4.,uv])
        log_lambda=np.log(100.)-8*math.pi**2/(ir*1.2)
        log_lambda+=sum((coeff[:-1]-coeff[1:])*np.log(matching/100.))/ir
        return log_lambda-np.log(t)
    slopes=[(running(np.exp(h),uv,9)-running(np.exp(-h),uv,9))/(2*h) for uv in (0,2)]
    np.testing.assert_allclose(slopes,[0,-2/9],atol=1e-9)
    return dict(AdS_mass_squared_L_squared=masses.tolist(),scalar_force_ratios=ratios,
                cassini_long_range_ratio=bound,universal_D0_fraction_tolerance=np.sqrt(3*bound)/4,
                gauge_scale_Einstein_slopes=slopes)


def flux_tower():
    # a=2*b*(M+1) caps both oscillator sums at the same integer M.
    samples=[]
    for b,cutoff,x in ((.6,4,0.),(.6,4,.8),(1.7,9,.8)):
        a=2*b*(cutoff+1)
        def heat(tau):
            scalar=sum(np.exp(-b*(2*i+1)*tau) for i in range(cutoff+1))**2
            return np.exp(-x*tau)*np.sinh(b*tau)**2*scalar
        for tau in (.02,.3,2.):
            np.testing.assert_allclose(heat(tau),.25*np.exp(-x*tau)*np.expm1(-a*tau)**2)
        area=quad(lambda z:.5*np.exp(-x*z)*(np.expm1(-a*z)/z)**2,0,np.inf)[0]
        finite=(xlogy(x,x)-2*xlogy(x+a,x+a)+xlogy(x+2*a,x+2*a))/2
        np.testing.assert_allclose(area,finite,rtol=1e-11)
        samples.append(dict(field=b,max_level=cutoff,separation_squared=x,response=finite))
    return samples


def double_sphere_action(spins,s):
    # Each pair names the spin on both spheres of one stack. Ordered stack
    # pairs give the exact full matrix trace (one orientation per Hom).
    u,v=math.exp(2*s),math.exp(-2*s)
    tree=sum((2*j+1)**2*j*(j+1)*(u*u+v*v) for j in spins)
    mixed,pure,scalar_min,charged_min=0.,0.,np.inf,np.inf
    def potential(x):
        assert x>=-1e-12
        return x*x*math.log(x) if x>1e-12 else 0.
    def trace_fun(x):
        return x*math.log(x) if x>1e-12 else 0.
    for i,j1 in enumerate(spins):
        for j,j2 in enumerate(spins):
            ls=np.arange(abs(j1-j2),j1+j2+.25,1.)
            for l in ls:
                for r in ls:
                    dl,dr=2*l+1,2*r+1
                    scalar=u*l*(l+1)+v*r*(r+1)
                    if scalar>0:
                        scalar_min=min(scalar_min,scalar)
                    def ferm_levels(k):
                        return [(k*k,(k+1)/(2*k+1)),((k+1)**2,k/(2*k+1))]
                    spinor=[(u*a+v*b,wa*wb) for a,wa in ferm_levels(l) for b,wb in ferm_levels(r)]
                    mixed+=2*dl*dr*(sum(w*trace_fun(x) for x,w in spinor)-trace_fun(scalar))
                    pure+=dl*dr*(2*potential(scalar)-8*sum(w*potential(x) for x,w in spinor))
                    def vector(k,scale):
                        modes=[(scalar-2*scale*k,2*k+3)]
                        if k>0:
                            modes.append((scalar+2*scale,2*k+1))
                        if k>=1:
                            modes.append((scalar+2*scale*(k+1),2*k-1))
                        return modes
                    for modes,other in ((vector(l,u),dr),(vector(r,v),dl)):
                        pure+=other*sum(w*potential(x) for x,w in modes)
                        if i!=j:
                            charged_min=min(charged_min,min(x for x,w in modes))
    return np.array([tree,mixed,pure,scalar_min,charged_min])


def double_spheres(j):
    spins=[j,j+.5]
    b,a,c,light,charged=double_sphere_action(spins,0.)
    curvs=[]
    for h in (.002,.001):
        second=(double_sphere_action(spins,h)[:3]+double_sphere_action(spins,-h)[:3]
                -2*np.array([b,a,c]))/h**2
        curvs.append([second[0]-2*b*second[1]/a,second[2]-2*c*second[1]/a])
    np.testing.assert_allclose(curvs[0],curvs[1],rtol=.0005)
    if j==.5:
        # Check one rectangular sector by direct matrices, independent of
        # the spin-coupling and degeneracy formulae used above.
        def coords(spin):
            m=np.arange(-spin,spin+1)
            up=np.diag(np.sqrt((spin-m[:-1])*(spin+m[:-1]+1)),-1)
            generators=[(up+up.T)/2,(up-up.T)/(2j),np.diag(m)]
            unit=np.eye(len(m))
            return [np.kron(x,unit) for x in generators]+[np.kron(unit,x) for x in generators]
        deriv=np.array([left_minus_right(x,y) for x,y in zip(coords(1.),coords(.5))])
        orb=sum(d@d for d in deriv)
        size=len(orb)
        spin=np.array([[2*(x@y-y@x) for y in deriv] for x in deriv])
        waves=np.kron(np.eye(6),orb)+spin.transpose(0,2,1,3).reshape(6*size,-1)
        np.testing.assert_allclose(eigh(waves,eigvals_only=True)[0],charged,atol=1e-12)
        dirac=np.einsum('ijk,ipq->jpkq',gammas(),deriv).reshape(8*size,-1)
        ferm=eigh(dirac,eigvals_only=True)**2
        spec=eigh(orb,eigvals_only=True)
        external=eigh(waves,eigvals_only=True)
        mixed_direct=2*(np.sum(xlogy(ferm,ferm))/8-np.sum(xlogy(spec,spec)))
        pure_direct=np.sum(external*xlogy(external,external))+2*np.sum(spec*xlogy(spec,spec))-np.sum(ferm*xlogy(ferm,ferm))
        isolated=(double_sphere_action(spins,0.)-double_sphere_action([j],0.)
                  -double_sphere_action([j+.5],0.))
        np.testing.assert_allclose(isolated[1:3],2*np.array([mixed_direct,pure_direct]),rtol=2e-12)
    # j labels the smaller physical stack, independent of the oscillator n.
    return dict(lower_spin=j,tree=b,summed_mixed=a,flat_internal_loop=c,
                first_scalar=light,lowest_charged_vector=charged,
                tree_shape_numerator=curvs[-1][0],loop_shape_numerator=curvs[-1][1],
                G_times_light_mass2=2*math.pi*light/a)


def main():
    result=dict(linear=bounded_linear_embedding(),
                spectra=[check_spectrum(n,h) for n,h in [(1,0),(1,1),(1,2),(2,0),(2,1),(3,0)]],
                products=[product_case(n,1,2) for n in (1,2,4)],
                four_links=[shape_cases(n) for n in (1,2)],
                onsite=[onsite_trial(n) for n in (1,2)],
                polarization=[null_polarization(n) for n in (1,2,3,4,6)],
                finite_shapes=[compact_minimum(n,False) for n in (3,4,5)],
                summed_search=[compact_minimum(n,True) for n in (2,4)],
                ordered_trace=determinant_check(),matter=flux_and_matter(),
                balanced_flux=flux_tower(),closed_matrix_spectra=[double_spheres(j) for j in (.5,1.,2.,4.)])
    path=Path(__file__).resolve().parents[1]/"verification"/"cat-projective-radius-results.json"
    path.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf8")
    print("Verified scalar spectra, physical polarizations, gravity response and material slopes.")


if __name__=="__main__":
    main()
