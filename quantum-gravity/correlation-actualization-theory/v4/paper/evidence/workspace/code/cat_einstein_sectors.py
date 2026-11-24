"""Check the Einstein equations of the measured metric and sector comparisons."""
import json
from fractions import Fraction as Q
from itertools import product
from math import factorial, prod
from pathlib import Path

import numpy as np
from scipy.integrate import quad

from cat_compact_interior import (anisotropic_data, bounce, clock_geometry,
                                   compact_energy, ranks, trajectory)

ROOT = Path(__file__).resolve().parents[1]


def einstein_from_connection():
    """Exact rational, off-equator coordinate jets; no field equations imposed."""
    checks=0
    for B,R,dB,dR,ddB,ddR in [(2,3,1,-2,-3,4),(1,4,-3,0,8,2),(5,2,0,0,0,0)]:
        B,R,dB,dR,ddB,ddR=map(Q,(B,R,dB,dR,ddB,ddR))
        sin,cos=Q(3,5),Q(4,5)
        metric=[-Q(1),B**2,R**2,R**2*sin**2]
        inverse=[1/v for v in metric]
        # first[k,i] and second[l,k,i] differentiate diagonal g_ii.
        first=np.full((4,4),Q(0),dtype=object)
        second=np.full((4,4,4),Q(0),dtype=object)
        first[0]=[0,2*B*dB,2*R*dR,2*R*dR*sin**2]
        first[2,3]=2*R**2*sin*cos
        second[0,0]=[0,2*(dB**2+B*ddB),2*(dR**2+R*ddR),2*(dR**2+R*ddR)*sin**2]
        second[0,2,3]=second[2,0,3]=4*R*dR*sin*cos
        second[2,2,3]=2*R**2*(cos**2-sin**2)
        conn=np.empty((4,4,4),dtype=object)
        dconn=np.empty((4,4,4,4),dtype=object)
        for k,i,j in np.ndindex(4,4,4):
            term=(j==k)*first[i,k]+(i==k)*first[j,k]-(i==j)*first[k,i]
            conn[k,i,j]=inverse[k]*term/2
            for l in range(4):
                dterm=(j==k)*second[l,i,k]+(i==k)*second[l,j,k]-(i==j)*second[l,k,i]
                dconn[l,k,i,j]=(inverse[k]*dterm-inverse[k]**2*first[l,k]*term)/2
        ricci=np.empty((4,4),dtype=object)
        for i,j in np.ndindex(4,4):
            ricci[i,j]=sum(dconn[k,k,i,j]-dconn[j,k,i,k]+sum(
                conn[k,k,l]*conn[l,i,j]-conn[k,j,l]*conn[l,i,k] for l in range(4)) for k in range(4))
        scalar=sum(inverse[i]*ricci[i,i] for i in range(4))
        E,T,C,D=-ddB/B,-ddR/R,dB*dR/(B*R),(1+dR**2)/R**2
        frame=[D+2*C,2*T-D,E+T-C,E+T-C]
        for i,j in np.ndindex(4,4):
            actual=ricci[i,j]-(metric[i]*scalar/2 if i==j else 0)
            assert actual==(abs(metric[i])*frame[i] if i==j else 0)
            checks+=1
        assert R*(frame[0]+frame[1])/B==-2*(ddR/B-dR*dB/B**2)
    return dict(exact_coordinate_tensor_entries=checks,off_equator=True)


def einstein_components(tides):
    axial, angular, mixed, sphere = tides
    return np.array([sphere+2*mixed,2*angular-sphere,axial+angular-mixed])


def null_budget(c):
    row = bounce(c)
    turn = row['turn_v']
    orbit = trajectory(c,0.,turn*1.01)
    def geometry(v):
        R,B,lapse,_,_,_,curv = clock_geometry(orbit(v),c)
        G = einstein_components(curv)
        return R/B*(G[0]+G[1])*lapse,G
    integral,error = quad(lambda v:geometry(v)[0],0,turn,epsabs=3e-11,epsrel=3e-11)
    np.testing.assert_allclose(integral,-2,atol=1e-9,rtol=0)
    at_surface,at_turn = [geometry(v)[1] for v in (0,turn)]
    assert max(abs(at_surface))<5e-11 and at_turn[0]+at_turn[1]<0
    return dict(x=c['x'],spin=c['spin_j'],share=c['S'],radius_at_turn=row['first_minimum_radius'],
                at_surface=at_surface.tolist(),at_turn=at_turn.tolist(),null_at_turn=at_turn[0]+at_turn[1],
                affine_weighted_null_integral=integral,quadrature_error=error)


def fixed_geometry_sectors():
    first = anisotropic_data(512.,.8,[5.9691791,9.0230583,2.1797419,19.9568834,46.9074762,-53.6049767])
    seed = first['compact_initial'].copy()
    for step in (1,2,3):
        seed[0]=first['compact_initial'][0]-.25*step
        second=anisotropic_data(512.,.8,seed,first['spin_j'])
        seed=second['compact_initial'].copy()
    energies=[compact_energy(np.array(c['compact_initial'][:3]),np.array(c['compact_initial'][3:]))
              for c in (first,second)]
    assert abs(energies[0]/energies[1]-1)>.02
    return dict(first=null_budget(first),second=null_budget(second),compact_energies=energies)


def motion_through_the_turn(points,steps):
    """Two projective measurements in one reduced sector, with the same H in between."""
    S,eps=.2,.2
    w0=np.sqrt(2*(1-2*S)/3)/S
    p0=S*w0**3
    w=np.linspace(-8,8,points,endpoint=False)
    p=2*np.pi*eps*np.fft.fftfreq(points,16/points)
    width=np.sqrt(eps/(2*np.sqrt(6)*w0))
    state=np.exp(-(w-w0)**2/(4*width**2)+1j*p0*w/eps)
    state/=np.linalg.norm(state)
    momentum=np.fft.fft(state,norm="ortho")
    weight=float(np.sum(abs(momentum[p>0])**2))
    momentum[p<=0]=0
    state=np.fft.ifft(momentum/np.sqrt(weight),norm="ortho")
    dt=.16/steps
    potential=np.exp(-1j*w**4*dt/(4*eps))
    kinetic=np.exp(-1j*p**2*dt/(2*eps))
    for _ in range(steps):
        state=potential*np.fft.ifft(kinetic*np.fft.fft(potential*state))
    mass=abs(np.fft.fft(state,norm="ortho"))**2
    after=float(np.sum(mass[p<0]))
    assert after>.99
    return dict(points=points,steps=steps,initial_positive_weight=weight,
                final_negative_given_positive=after)


def signatures():
    target=np.diag([-1.]+[1.]*9)
    symplectic=np.kron(np.eye(2),[[0.,1.],[-1.,0.]])
    rows=[]
    for tilt in (0.,.5,1.,1.5,2.):
        embedding=np.zeros((10,4))
        embedding[0,0]=tilt
        embedding[1:5]=np.eye(4)
        h=embedding.T@target@embedding
        H=symplectic.T@h@symplectic
        eig=np.linalg.eigvalsh(H)
        assert np.allclose(np.sort(np.diag(h)),eig)
        rows.append(dict(tilt=tilt,negative=int(sum(eig<0)),zero=int(sum(eig==0)),positive=int(sum(eig>0)),
                         determinant=np.linalg.det(H)))
    return rows


def flat_patch_algebra():
    """Check the bidifferential Moyal formula exactly on polynomials of degree <=4.

    The parameter stands for i*hbar/2; rational evaluations avoid rounding.
    Algebraic checks cannot identify a global exotic differentiable structure.
    """
    unit=(0,0,0,0)
    coordinates=[{tuple(int(i==k) for i in range(4)):Q(1)} for k in range(4)]
    field={(2,1,0,1):Q(2),(0,0,2,0):Q(-3),(1,0,0,0):Q(1)}
    def plus(polys):
        answer={}
        for factor,poly in polys:
            for key,value in poly.items():
                answer[key]=answer.get(key,0)+factor*value
        return {k:v for k,v in answer.items() if v}
    def differentiate(poly,i):
        return {tuple(n-(k==i) for k,n in enumerate(e)):c*e[i] for e,c in poly.items() if e[i]}
    def star(left,right,s):
        result={}
        for a,av in left.items():
            for b,bv in right.items():
                for n in product(*(range(1+min(a[i],b[i^1])) for i in range(4))):
                    out=tuple(a[i]+b[i]-n[i]-n[i^1] for i in range(4))
                    coeff=prod(factorial(a[i])//factorial(a[i]-n[i])
                               * (factorial(b[i^1])//factorial(b[i^1]-n[i]))
                               //factorial(n[i]) for i in range(4))
                    weight=s**sum(n)*(-1)**(n[1]+n[3])*coeff
                    result[out]=result.get(out,0)+av*bv*weight
        return {k:v for k,v in result.items() if v}
    tests=0
    for s in (Q(1,3),Q(-2,5)):
        bracket=lambda f,g:plus([(1,star(f,g,s)),(-1,star(g,f,s))])
        for i,x in enumerate(coordinates):
            for j,y in enumerate(coordinates):
                const=bracket(x,y)
                expected=(2*s*(-1)**(i%2)) if j==i^1 else 0
                assert const==({unit:expected} if expected else {})
                assert bracket(x,const)=={}
                tests+=1
            assert bracket(x,field)==plus([(2*s*(-1)**(i%2),differentiate(field,i^1))])
        wave=plus([((-1 if i==0 else 1),bracket(x,bracket(x,field))) for i,x in enumerate(coordinates)])
        expected=plus([(4*s*s*(-1 if i==0 else 1),differentiate(differentiate(field,i^1),i^1)) for i in range(4)])
        assert wave==expected and wave
        assert star(star(field,field,s),coordinates[1],s)==star(field,star(field,coordinates[1],s),s)
    return dict(coordinate_commutators=tests,ordinary_and_star_wave_identical=True,
                exact_polynomial_associativity=True)


def checks():
    u=1.
    s=1+u*u
    a=np.sqrt(s)
    trace=2*(a*a/s**2-1/s)
    shear=np.sqrt(s*s+1)*abs(u)/s**2.5
    assert abs(trace)<1e-14 and abs(shear-np.sqrt(5/32))<1e-14
    # Static product, R0=2. Gaussian Maxwell units. Store 8*pi*G*rho.
    R0=2.
    curvature=np.array([1.,-1.,0.])/R0**2
    cosmological=1/(2*R0**2)
    source=cosmological*np.array([1.,-1.,1.])
    np.testing.assert_allclose(curvature+cosmological*np.array([-1.,1.,1.]),source)
    wave=[motion_through_the_turn(1024,320),motion_through_the_turn(2048,640)]
    np.testing.assert_allclose(wave[0]['final_negative_given_positive'],wave[1]['final_negative_given_positive'],
                               atol=1e-8,rtol=0)
    return dict(coordinate_tensor=einstein_from_connection(),matched=null_budget(ranks(512.,.2)),
                fixed_rank=fixed_geometry_sectors(),same_sector_momentum=wave,
                vacuum_plane_wave=dict(u=u,trace=trace,tidal_amplitude=shear),
                einstein_maxwell_product=dict(radius=R0,Lambda=cosmological,eight_pi_G_rho=source[0]),
                fixed_target=signatures(),restricted_flat_algebra=flat_patch_algebra())


if __name__=='__main__':
    path=ROOT/'verification/cat-einstein-sectors-results.json'
    path.write_bytes((json.dumps(checks(),indent=2,allow_nan=False)+'\n').encode('utf8'))
