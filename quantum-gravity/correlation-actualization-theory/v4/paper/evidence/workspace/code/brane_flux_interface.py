"""Wrapped-brane mass threshold, gravitational receipt and change of radial channel.

Lengths are in string lengths, energies in inverse string lengths. The two exits
belong to a proposed gravitational contact, not to the ordinary D-brane action.
"""
from math import exp, hypot, pi, sqrt
from pathlib import Path
import json

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.integrate import solve_ivp

ROOT = Path(__file__).resolve().parents[1]


def gap(mass, unit, total):
    """Rationalized difference of BPS masses for two unit windings."""
    lower, odd = divmod(total, 2)
    if not odd:
        return 0.0
    left, right = hypot(mass, lower*unit), hypot(mass, (lower+1)*unit)
    parent = hypot(2*mass, total*unit)
    dot = mass**2 + lower*(lower+1)*unit**2
    return 2*(mass*unit)**2/((left+right+parent)*(left*right+dot))


def spectrum(length=40., coupling=.1, total=3):
    tension = 1/(2*pi*coupling)
    mass = unit = tension*length
    circumference = length*hypot(2, total)
    omega = 4*pi/circumference
    newton = 8*pi**6*coupling**2/length**6
    parent = hypot(2*mass, total*unit)
    delta = gap(mass, unit, total)
    transverse_image = length**2/(2*pi*circumference)
    dual_y = 4*pi*pi/length
    open_metric = 1+(total/2)**2
    adjoint_pair = 2*pi/(max(length, dual_y)*sqrt(open_metric))
    width = 4*newton*omega**3
    return dict(total=total, coupling=coupling, length=length, mass=parent, gap=delta,
                omega=omega, width=width, gap_over_line=delta/omega, width_over_line=width/omega,
                separation_in_halfwidths=2*delta/width, bulk_kk=2*pi/length, image_threshold=transverse_image,
                adjoint_pair=adjoint_pair, newton=newton, gravitational_radius=2*newton*parent)


def charge_checks():
    error = 0.
    for mass in (.2, 1., 7.):
        for unit in (.1, 1., 19.):
            for total in range(-19, 21):
                exact = gap(mass, unit, total)
                parent = hypot(2*mass,total*unit)
                enumerated = min(hypot(mass,n*unit)+hypot(mass,(total-n)*unit)
                                 for n in range(-45,46))
                error = max(error, abs(exact-(enumerated-parent)))
    assert error < 2e-13
    samples = [spectrum(total=n) for n in range(1,100,2)]
    last = max(row["total"] for row in samples if row["gap_over_line"] > 1)
    return dict(max_absolute_mass_error=error, last_odd_below_fission=last,
                adjacent=[spectrum(total=n) for n in (last,last+2)])


def holonomies():
    identity = np.eye(2)
    x = np.array([[0.,1.],[1.,0.]])
    z = np.diag([1.,-1.])
    variations = [(z,x), (identity,z)]
    dimensions = []
    for u,v in variations:
        # Vectorization of T U_source = U_target T, using column-major indices.
        system = np.vstack([np.kron(t.T,identity)-np.kron(identity,s)
                            for t,s in zip((z,x),(u,v))])
        dimensions.append(4-int(np.linalg.matrix_rank(system)))
    p = (identity+z)/2
    assert dimensions==[1,0]
    assert np.array_equal(x@p@x,identity-p) and np.array_equal(z@p@z,p)
    assert np.array_equal(x@z@x@z,-identity)
    return dict(complex_intertwiner_dimensions=dimensions, unordered_pair_survives=True)


def spin_basis():
    basis = [np.diag([1.,-1.,0.])/sqrt(2),np.diag([1.,1.,-2.])/sqrt(6)]
    for j,k in ((0,1),(0,2),(1,2)):
        e = np.zeros((3,3));e[j,k]=e[k,j]=1/sqrt(2)
        basis.append(e)
    return np.array(basis)


def angular_checks():
    basis = spin_basis()
    mu,polar_weights = leggauss(10)
    sums = {k:np.zeros((5,5)) for k in ("tensor","other_metric","dilaton","rr","kk","cross_kk","overlap")}
    isometry_error = 0.
    slope = np.array([2.,3.])/sqrt(13)
    alt = np.array([2.,-3.])/sqrt(13)
    def vertex(e,n,project,w):
        # 3 external coordinates plus the two used internal coordinates.
        # Extend by four zero internal rows only for the 8D transverse trace.
        left = np.vstack([project,np.outer(w,n)])
        right = np.vstack([project,-np.outer(w,n)])
        return left@e@right.T
    def gram(a,b):
        return a.reshape(5,-1)@b.reshape(5,-1).T
    for cosine,weight in zip(mu,polar_weights):
        for phase in np.arange(20)*pi/10:
            n = np.array([sqrt(1-cosine**2)*np.cos(phase),sqrt(1-cosine**2)*np.sin(phase),cosine])
            p = np.eye(3)-np.outer(n,n)
            first = np.array([vertex(e,n,p,slope) for e in basis])
            second = np.array([vertex(e,n,p,alt) for e in basis])
            sym = (first+first.transpose(0,2,1))/2
            anti = first-sym
            trace = np.trace(first,axis1=1,axis2=2)
            ext = sym[:,:3,:3]
            ext_tt = ext - np.einsum("a,ij->aij",np.trace(ext,axis1=1,axis2=2)/2,p)
            scalar = np.outer(trace,trace)/8
            tensor = gram(ext_tt,ext_tt)
            contributions=dict(tensor=tensor,other_metric=gram(sym,sym)-scalar-tensor,dilaton=scalar,
                               rr=gram(anti,anti),kk=2*gram(anti[:,:3,4],anti[:,:3,4]),
                               cross_kk=-2*gram(anti[:,:3,4],anti[:,:3,4]),overlap=gram(first,second))
            for k,value in contributions.items():
                sums[k]+=weight*value/40
            isometry_error=max(isometry_error,float(np.max(np.abs(gram(first,first)-np.eye(5)))))
    c=float(slope@alt)
    expected=[2/5,2/15,1/15,2/5,18/65,-18/65,(7+6*c+2*c*c)/15]
    residual=max(float(np.max(np.abs(value-target*np.eye(5)))) for value,target in zip(sums.values(),expected))
    assert max(isometry_error,residual)<1e-13
    return dict(directional_isometry_error=isometry_error,integrated_gram_error=residual,
                angular_fractions={k:float(np.trace(value)/5) for k,value in sums.items()})


def absorption():
    same, opposite = 44/65,8/65
    peaks=[]
    for overlap in (same,opposite):
        sol=solve_ivp(lambda t,b:-b/2+overlap*exp(-t/2),(0.,2.),[0.],rtol=2e-12,atol=1e-14)
        measured=float(sol.y[0,-1]**2)
        assert abs(measured-4*exp(-2)*overlap**2)<2e-13
        peaks.append(measured)
    inner=opposite/same
    return dict(metric_emission_probability=same, conditional_overlap=inner,
                discrimination_error=(1-sqrt(1-inner**2))/2,material_peaks=peaks,
                peak_ratio=peaks[0]/peaks[1], which_species_peak=4*exp(-2)*((2/5)**2+(18/65)**2))


def horizon(row):
    mass,omega,delta=row["mass"],row["omega"],row["gap"]
    incoming=mass+omega
    photon=(delta-omega)*(2*mass+delta+omega)/(2*incoming)
    radius=1e5
    asymptotic=1/(4*pi*radius)
    ratio=asymptotic/photon
    zcrit=sqrt(ratio*(2-ratio))
    # Stable outgoing Doppler factor, independent root via energy conservation.
    local=asymptotic*(1+sqrt(1-zcrit**2))/zcrit**2
    assert abs(sqrt(incoming**2+2*incoming*local)-(mass+delta))<2e-12
    zstop=incoming/(mass+delta)
    return dict(radius=radius, packet_at_infinity=asymptotic, photon_threshold=photon,
                critical_lapse=zcrit, inward_energy_at_horizon=asymptotic/2,
                static_stopping_lapse=zstop, stopping_radius_in_horizon_radii=1/(1-zstop*zstop),
                static_acceleration_over_line_at_y_one=2*pi)


def draw():
    fig,axs=plt.subplots(1,2,figsize=(8.5,3.25),layout="constrained")
    ax=axs[0]
    winding=list(range(1,50,2))
    for coupling in (.05,.1,.3):
        ax.plot(winding,[spectrum(total=n,coupling=coupling)["gap_over_line"] for n in winding],
                marker=".",label=rf"$g_B={coupling}$")
    ax.axhline(1,color="black",ls="--",lw=.8)
    ax.set(yscale="log",xlabel="Odd D0 charge",ylabel=r"Fission threshold / line energy $\Delta/\Omega$")
    ax.legend(frameon=False,fontsize=8)
    t=np.linspace(0,8,240)
    ax=axs[1]
    for overlap,label in ((44/65,"Same slope"),(8/65,"Opposite slope")):
        ax.plot(t,overlap**2*t**2*np.exp(-t),label=label)
    ax.plot(t,((2/5)**2+(18/65)**2)*t**2*np.exp(-t),ls="--",label="Species read first")
    ax.set(xlabel=r"Time after arrival $\Gamma t$",ylabel="Receiver excitation probability",ylim=(0,.27))
    ax.legend(frameon=False,fontsize=8)
    destination=ROOT/"manuscripts"/"brane_flux_interface.pdf"
    destination.parent.mkdir(parents=True,exist_ok=True)
    fig.savefig(destination,metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)


def main():
    example=spectrum()
    assert example["omega"] < min(example[x] for x in ("gap","bulk_kk","image_threshold"))
    assert abs(example["omega"]-example["adjoint_pair"]) < 1e-14
    checks=charge_checks()
    report=dict(example=example,charges=checks,holonomies=holonomies(),angular=angular_checks(),
                absorption=absorption(),horizon=horizon(example), low_energy_horizon=dict(spectrum=spectrum(total=11),
                collision=horizon(spectrum(total=11))))
    draw()
    target=ROOT/"verification"/"brane-flux-interface-results.json"
    target.write_text(json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf8")
    print("Wrapped flux, emission polarizations, material absorption and horizon kinematics verified.")


if __name__=="__main__":
    main()
