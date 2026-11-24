"""Finite tidal readout, recoil-resolved Hawking comparison and two-photon endpoint."""
import argparse
import itertools
import json
import math
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import expm
from scipy.optimize import brentq
from scipy.special import roots_legendre, zeta

ROOT = Path(__file__).resolve().parents[1]


def material():
    # Two identical sites with anchored positions. Check a covariant lattice Laplacian.
    swap = np.eye(4)[[0, 2, 1, 3]]
    odd = (np.eye(4) - swap) / 2
    bare = np.kron(np.diag([0., 1.]), np.eye(2)) + np.kron(np.eye(2), np.diag([0., 1.]))
    positions = np.linspace(-1., 2., 15)
    t = np.clip(positions, 0., 1.)
    profile = t**3 * (10. - 15.*t + 6.*t*t)
    bases = np.array([np.eye(4) + np.expm1(1j*math.pi*f)*odd for f in profile])
    h0 = np.kron(np.diag(np.full(15, 2.)) - np.diag(np.ones(14), 1)
                 - np.diag(np.ones(14), -1), np.eye(4)) + np.kron(np.eye(15), bare)
    basis = np.zeros_like(h0, dtype=complex)
    linked = np.kron(np.eye(15), 2*np.eye(4) + bare).astype(complex)
    for i, unitary in enumerate(bases):
        here = slice(4*i, 4*i+4)
        basis[here, here] = unitary
        if i:
            before = slice(4*i-4, 4*i)
            linked[here, before] = -unitary @ bases[i-1].conj().T
            linked[before, here] = linked[here, before].conj().T
    core = float(np.max(abs(linked - basis@h0@basis.conj().T)))
    evolution = float(np.max(abs(expm(-.73j*linked) - basis@expm(-.73j*h0)@basis.conj().T)))
    assert max(core, evolution, np.max(abs(bases[-1]-swap))) < 1e-12
    thermal = np.kron(np.diag([.23,.77]),np.diag([.23,.77]))
    unchanged = float(np.linalg.norm(swap@thermal@swap.T-thermal,ord="nuc"))/2
    assert unchanged == 0.
    # Marginal radial geodesic, dimensionless proper time in r_s/c.
    start, end = 1.5, math.sqrt(2.)
    duration = (2/3)*(start**1.5-end**1.5)
    radius = lambda time: (start**1.5-1.5*time)**(2/3)
    strain = lambda radius: .2*(radius/start)**2 + .8*math.sqrt(start/radius)-1
    crossing = brentq(lambda t: strain(radius(t))-5e-4, 0., duration)
    sol = solve_ivp(lambda t,y: [y[1], y[0]/radius(t)**3], (0,duration), [1.,0.],
                    method="DOP853", rtol=1e-12, atol=1e-14, dense_output=True)
    assert abs(sol.sol(duration)[0]-1-strain(end)) < 4e-14
    rows = []
    for mass_solar in (3., 1e6):
        unit = 2*4.925490947e-6*mass_solar
        omega = 5000./5e-5
        tide = 1/(unit**2*end**3)
        feedback = tide*unit*duration/omega
        bound = 2*tide/(omega**2*(1-feedback))
        rows.append(dict(solar_masses=mass_solar, duration_s=duration*unit,
                         margin_s=(duration-crossing)*unit, free_strain=strain(end),
                         grain_elastic_strain_upper=bound,
                         grain_elastic_stroke_m=5e-5*bound))
    return dict(laplacian_residual=core,propagator_residual=evolution,fall=rows,
                unmarked_thermal_trace_distance=unchanged, identical_in_ten_unbiased_pairs=2**-10)


def floor_moment(p):
    return float(zeta(p+1)/(p+1))


def rare_mode(mmax, grid, repetitions, order):
    """Probability of any marked graviton along a photon-led, recoil-resolved cascade."""
    nodes, weights = roots_legendre(order)
    t, weights = (nodes+1)/2, weights/2
    j = np.arange(1,repetitions+1)[:,None]
    x = t[None,:]/j
    # n(x,m)=sum_{j<=1/x} exp(-4*pi*m^2*j*x). One actual photon per jump.
    masses = np.linspace(0,mmax,grid+1)
    prob = np.zeros(grid+1)
    first = np.zeros_like(prob)
    for i,m in enumerate(masses[1:],1):
        factor = weights[None,:]*np.exp(-4*math.pi*m*m*t)/j
        y = m*m*x
        low, high = (4/9)*y**4, (4/225)*y**6
        photon = 6*factor*low/(1+low)
        graviton = 10*factor*high/(1+high)
        total = photon.sum()+graviton.sum()
        p = photon/total
        first[i] = graviton.sum()/total
        where = i*np.sqrt(1-x)
        left = np.floor(where).astype(int)
        right = left+1
        frac = where-left
        diagonal = float(np.sum(np.where(right==i,p*frac,0.)))
        prob[i] = (first[i]+np.sum(p*((1-frac)*prob[left]+frac*prob[right])))/(1-diagonal)
    # Analytic majorant for the full infinite sum, with the leading channel conditioning.
    a,b = 4/9,4/225
    loss = (2*floor_moment(5)-floor_moment(6))/floor_moment(4)
    penalty = math.exp(4*math.pi*mmax**2)*(1+a*mmax**8)
    upper = (10*b/(6*a))*floor_moment(6)/floor_moment(4)*penalty**2*mmax**4/loss
    assert 0 < first[-1] < prob[-1] < upper < 1
    return dict(mass=mmax,grid=grid,terms=repetitions,order=order,
                first=float(first[-1]),ever=float(prob[-1]),upper=upper), (masses,prob)


def endpoint():
    # Signature (+---) for evaluating the flat-space vertices via E and B.
    # In the two-photon rest frame the parent and daughter have identical spatial momentum.
    def tensor(k, h):
        cross = np.cross(k,[0.,1.,0.])
        cross = cross/np.linalg.norm(cross)
        second = np.cross(k,cross)
        electric = (cross+1j*h*second)/math.sqrt(2)
        magnetic = np.cross(k,electric)
        return electric, magnetic

    checks=[]
    for cosine in (-.82,-.24,.37,.81):
        k = np.array([math.sqrt(1-cosine*cosine),0.,cosine])
        for h1,h2 in itertools.product((-1,1),repeat=2):
            e,b = tensor(k,h1)
            f,c = tensor(-k,h2)
            # Overall phases and coupling normalizations are conventional.
            scalar = np.dot(e,f)-np.dot(b,c)
            pseudo = np.dot(e,c)+np.dot(f,b)
            tzz = -2*e[2]*f[2]-2*b[2]*c[2]+np.dot(e,f)+np.dot(b,c)
            if h1==h2:
                checks.extend([abs(tzz), abs(abs(scalar)-2.),abs(pseudo+1j*h1*scalar)])
            else:
                checks.extend([abs(scalar),abs(pseudo),abs(abs(tzz)-2*(1-cosine**2))])
    tensor_error = float(max(checks))
    assert tensor_error < 1e-12
    rows=[]
    for q in (.3,.5,.8):
        ymax = (1-q)**2
        def lam(y):
            return (ymax-y)*((1+q)**2-y)
        integrated = quad(lambda y: lam(y)**2.5,0,ymax,epsabs=1e-15)[0]
        D8 = integrated/(480*math.pi**3)
        D5 = 1/(32*math.pi)
        # Independent fully differential phase-space integral and simple dipole escape test.
        n,w = roots_legendre(56)
        def density(y, filt):
            l = lam(y)
            e1 = (1-q*q+y+math.sqrt(l)*n)/4
            e2 = (1-q*q+y-math.sqrt(l)*n)/4
            loss = (2*e1)**4*(2*e2)**4 if filt else np.ones_like(n)
            return l**2.5*float(np.sum(w*(1-n*n)**2*loss))/2/(256*math.pi**3)
        direct = quad(lambda y:density(y,False),0,ymax,epsabs=1e-15)[0]
        escaped = quad(lambda y:density(y,True),0,ymax,epsabs=1e-19)[0]
        assert abs(direct-D8)<1e-14 and 0<escaped<D8
        rows.append(dict(daughter_ratio=q,D8=D8,D5=D5,ratio=D8/D5,
                         dipole_escape_ratio=escaped/D8))
    # Illustrative units set the two initial widths equal; test long waiting times explicitly.
    q=.5
    survival=1.
    survival_array=[1.]
    mean_proper=0.
    mean_inertial_upper=0.
    for j in range(24):
        m=q**j
        mean_proper+=survival/(m**3*(1+m**6))
        mean_inertial_upper+=survival/(m**4*(1+m**6))
        survival*=m**6/(1+m**6)
        survival_array.append(survival)
    assert 1 < mean_proper < mean_inertial_upper
    return dict(helicity_tensor_residual=tensor_error,phase_space=rows,
                mass_ratio=q, survival_first_six=survival_array[:7],
                expected_proper_in_initial_terminal_lifetimes=mean_proper,
                inertial_time_upper_in_same_units=mean_inertial_upper)


def crossed_tower():
    # At fixed two-photon invariant energy, the squared amplitude contributes
    # lambda^2 and the final two-body measure contributes sqrt(lambda).
    q=.5
    mass=.2*q**np.arange(100)
    lam=(1.-((1+q)*mass)**2)*(1.-((1-q)*mass)**2)
    weights=lam**2.5
    flat_partial=[float(sum(weights[:n])) for n in (8,32,96)]
    tapered_partial=[float(sum((weights*q**(2*np.arange(100)))[:n])) for n in (8,32,96)]
    assert flat_partial[-1]-flat_partial[1]>63.99
    assert 0<tapered_partial[-1]<1/(1-q*q) and abs(tapered_partial[-1]-tapered_partial[1])<1e-14
    return dict(level_counts=[8,32,96],constant_vertex_partial_sums=flat_partial,
                mass_tapered_partial_sums=tapered_partial,geometric_upper=1/(1-q*q))


def hidden_record():
    # Overlapping radiation states for three indistinguishable clock histories.
    wave=np.array([[1.,0.,0.],[.8,.6,0.],[.4,.3,math.sqrt(.75)]])
    prob=np.array([.2,.5,.3])
    gram=np.sqrt(prob[:,None]*prob[None,:])*(wave@wave.T)
    plus=np.zeros((6,3))
    minus=np.zeros_like(plus)
    plus[:3]=wave.T*np.sqrt(prob)
    minus[3:]=plus[:3]
    residual=float(max(np.max(abs(plus.T@plus-gram)),np.max(abs(minus.T@minus-gram)),
                       np.max(abs(plus.T@minus))))
    assert residual<1e-14
    return dict(unseen_history_gram_residual=residual,history_gram_off_diagonal=gram[0,1],
                bell_fidelity_if_helicity_is_measured=.5)


def invariant(vector):
    return vector[0]**2-np.dot(vector[1:],vector[1:])


def boost(vector, parent):
    # Rotationless Lorentz boost from the parent's rest frame into the analysis frame.
    mass = math.sqrt(invariant(parent))
    velocity = parent[1:]/parent[0]
    gamma = parent[0]/mass
    dot = np.dot(velocity,vector[1:])
    return np.r_[gamma*(vector[0]+dot), vector[1:]+
                 (gamma*vector[0]+gamma**2/(gamma+1)*dot)*velocity]


def pairing():
    def unit(axis,phase):
        polar = 1.3+0.9*math.sin(axis+phase)
        return np.array([math.sin(polar)*math.cos(axis), math.sin(polar)*math.sin(axis),
                         math.cos(polar)])
    q=.5
    rows=[]
    for stages in (2,3,4):
        gap=1.
        err=0.
        for sample in range(48):
            parent=np.array([1.,0.,0.,0.])
            photons=[]
            for stage in range(stages):
                mass=q**stage
                a=math.sqrt(2)*(sample+1)+1.71*stage
                b=math.sqrt(3)*(stage+1)-.48*sample
                direction=unit(b,a)
                if stage==stages-1:
                    pair=parent
                    root=mass
                else:
                    root=mass*(.16+.23*(1+math.sin(a+.7*b))/2)
                    y=(root/mass)**2
                    energy=mass*(1-q*q+y)/2
                    path=unit(a,b)
                    pair=boost(np.r_[energy,math.sqrt(energy**2-root**2)*path],parent)
                photons.extend([boost(np.r_[root/2,sign*root/2*direction],pair)
                                for sign in (1.,-1.)])
                parent=parent-pair
            observed=list(range(2*stages-1,-1,-1))
            current=np.sum(photons,axis=0)
            for stage in range(stages-1):
                mass=q**stage
                choices=[]
                for i,j in itertools.combinations(observed,2):
                    rest=current-photons[i]-photons[j]
                    choices.append((abs(invariant(rest)/mass**2-q*q),{i,j}))
                choices.sort(key=lambda item:item[0])
                assert choices[0][1]=={2*stage,2*stage+1}
                gap=min(gap,choices[1][0])
                err=max(err,choices[0][0])
                for k in choices[0][1]:
                    observed.remove(k)
                    current-=photons[k]
        assert err<2e-13 and gap>100*err
        rows.append(dict(stages=stages,configurations=48,correct_residual_max=err,
                         smallest_wrong_mass_squared_gap=gap))
    C6=quad(lambda y:y*y*math.sqrt((.25-y)*(2.25-y)),0,.25,epsabs=1e-15)[0]/(512*math.pi**3)
    return dict(examples=rows,C6_for_half_mass=C6)


def make_figure(path,curve):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig,(a,b)=plt.subplots(1,2,figsize=(8.1,3.0),layout="constrained")
    r=np.linspace(1.5,math.sqrt(2),201)
    elapsed=(1.5**1.5-r**1.5)*2/3*(6*4.925490947)
    a.plot(elapsed,1e3*(.2*(r/1.5)**2+.8*np.sqrt(1.5/r)-1),color="#216074",label="Free separation")
    a.axhline(.5,color="#a24524",ls="--",label="Illustrative full stroke")
    a.set(xlabel=r"Proper time from photon sphere ($\mu$s)",ylabel="Separation change (parts per thousand)")
    a.legend(frameon=False,fontsize=8)
    m,p=curve
    b.plot(m,100*p,color="#574085")
    b.set(xlabel="Initial mass (Planck masses)",ylabel="Any direct graviton emission (%)")
    b.ticklabel_format(style="plain",axis="y")
    fig.savefig(path)
    plt.close(fig)


if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--figure",type=Path)
    args=ap.parse_args()
    mat=material()
    coarse,_=rare_mode(.2,180,32,16)
    fine,curve=rare_mode(.2,360,64,28)
    assert abs(coarse["ever"]-fine["ever"])<2e-8
    tail=endpoint()
    report=dict(material=mat,rare_quadrupole=[coarse,fine],endpoint=tail,
                code=hidden_record(),pair_order=pairing(),crossed_species=crossed_tower())
    (ROOT/"verification/material-charge-readout-results.json").write_text(
        json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf8")
    if args.figure:
        make_figure(args.figure,curve)
    print("Tidal receipt, recoil, helicity amplitudes and evaporation checks passed.")
