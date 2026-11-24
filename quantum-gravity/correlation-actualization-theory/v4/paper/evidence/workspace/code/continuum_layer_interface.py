"""Continuously many Born-weighted layers at a gravitational contact.

Use physical phases of the joint layer configuration. The input is never a
choice of ensemble decomposition of an ordinary density matrix.
"""
from math import ceil, comb, erfc, exp, expm1, floor, gcd, pi, sqrt
from pathlib import Path
import json
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.constants import G, c, hbar
from scipy.integrate import quad
from scipy.special import j0, kv

ROOT=Path(__file__).resolve().parents[1]


def kernel(b=60.,radius=10.,speed=.1,area=2e12,rank=3):
    # Two material populations, each with a continuum of alternative layers.
    # Mass and M2 harmonic coefficient are for the parent material in each.
    mass=rank*area/(4*pi*pi)
    charge=32*pi*pi*rank
    j=np.arange(1,25,dtype=float)
    x=j*b/radius
    energy=mass*charge*speed**4*np.exp(-x)*(x*x+3*x+3)/(64*radius*b**5)
    phase=mass*charge*speed**3*j*j*kv(2,x)/(32*radius**3*b**2)
    return j,energy,phase,mass,charge


def exchange():
    b,radius,speed=60.,10.,.1
    j,energy,phase,mass,charge=kernel()
    grid=2*pi*np.arange(4096)/4096
    fourier=phase@np.cos(np.outer(j,grid))
    density=np.abs(np.fft.fft(np.exp(1j*fourier))/len(grid))**2
    charges=np.rint(np.fft.fftfreq(len(grid))*len(grid)).astype(int)
    assert abs(np.sum(density)-1)<3e-15
    measured={}
    for rank in (2,3,4,5):
        selected=float(density[(2*charges)%rank==0].sum())
        order=rank//gcd(rank,2)
        autocorr=0.
        for index in range(order):
            shifted=phase@np.cos(np.outer(j,grid+2*pi*index/order))
            autocorr+=float(np.mean(np.cos(shifted-fourier)))/order
        assert abs(selected-autocorr)<3e-14
        measured[str(rank)]=selected
    # Independent image-space action, removing its common zero mode.
    images=np.arange(-60,61)
    grid2=grid[::64]
    profile=np.sum((b*b+radius**2*(grid2[:,None]+2*pi*images)**2)**(-2.5),axis=1)
    prefactor=3*pi*mass*speed**3*charge/64
    err=float(np.max(np.abs(prefactor*(profile-profile.mean())-(fourier[::64]-fourier[::64].mean()))))
    assert err<2.e-8
    return dict(first_phases=phase[:4].tolist(),radial_weights=measured,
        rank_three_one_harmonic=(1+2*j0(sqrt(3)*phase[0]))/3,
        image_phase_error=err,field_strength_upper=float(charge/b**6*(1+2*b/radius)),
        eikonal_recoil_time_ratio=b/(speed*mass*radius**2))


def continuum():
    j,energy,phase,mass,charge=kernel()
    sigma_a,sigma_b=.30,1.30
    # Exact positive continuum functional for two independent equal wrapped
    # normals on the circle. Width here is conditional on physical layer data.
    def functional(sigma):
        return float(energy@(-np.expm1(-(j*sigma)**2)))
    exact_a,exact_b=functional(sigma_a),functional(sigma_b)
    # A conservative bound for non-Gaussian distributions: 1-cos(x) <= x^2/2.
    # B needs only its first relational Fourier moment.
    ceiling=1.2*sigma_a*sigma_a*float(energy@(j*j))
    bottom=.8*float(energy[0])*(1-exp(-sigma_b*sigma_b))
    spacing=4*pi/sqrt(2.e12)
    rows=[]
    for size in (48,96,192):
        theta=2*pi*np.arange(size)/size-pi
        diff=theta[:,None]-theta[None,:]
        pair=sum(strength*(1-np.cos(index*diff)) for index,strength in zip(j,energy))
        for sigma,exact in ((sigma_a,exact_a),(sigma_b,exact_b)):
            prob=sum(np.exp(-.5*((theta+2*pi*image)/sigma)**2) for image in range(-5,6))
            prob=prob/prob.sum()
            direct=float(prob@pair@prob)
            assert abs(direct-exact)<1e-12
            rows.append([size,sigma,direct])
    # Splitting one physical weight into arbitrary co-located subweights.
    theta=np.array([.1,.1,1.4,-2.])
    weights=np.array([.19,.12,.28,.41])
    def energy_of(w,th):
        means=np.exp(1j*np.outer(j,th))@w
        return float(energy@(1-np.abs(means)**2))
    ref=energy_of(weights,theta)
    assert abs(energy_of(np.array([.31,.28,.41]),theta[[0,2,3]])-ref)<2e-17
    # Position-dependent, positive pair interaction rather than a constant kernel.
    th=2*pi*np.arange(140)/140-pi
    dx=th[:,None]-th[None,:]
    pair=sum(h*(1-np.cos(n*dx)) for n,h in zip(j,energy))
    modulated=pair*(1+.19*np.cos(th[:,None]+2*th[None,:]))
    nonuniform=[]
    for sigma in (sigma_a,sigma_b):
        p=sum(np.exp(-.5*((th+2*pi*t)/sigma)**2) for t in range(-4,5));p/=p.sum()
        nonuniform.append(float(p@modulated@p))
    assert nonuniform[0]<=ceiling<bottom<=nonuniform[1]
    return dict(harmonics=energy[:4].tolist(),a_exact=exact_a,b_exact=exact_b,
                thin_ceiling=ceiling,thick_floor=bottom,mode_spacing=spacing,
                guaranteed_mode_interval=[floor(ceiling/spacing)+1,ceil(bottom/spacing)-1],
                grid_checks=rows,nonuniform=nonuniform,
                relative_acceleration_phase_bound=float((energy@(j*j))*(60/.1)**2/(.5*mass*10**2)),
                resolution_invariance_error=abs(energy_of(np.array([.31,.28,.41]),theta[[0,2,3]])-ref))


def finite_contact(scale, speed):
    # Frequency of a real material clock reads E-D during a grazing passage.
    # A spatially extended patch adds action, independent of layer count.
    b,radius=60.,10.
    new_area=2e12*scale*(.1/speed)**3
    energy_scale=scale*speed/.1
    E=180*4*pi/sqrt(2e12)*energy_scale
    n_mode=max(1,round(E*sqrt(new_area)/(4*pi)))
    E=n_mode*4*pi/sqrt(new_area)
    duration=.03*b/speed
    points=16384
    step=32*duration/points
    t=(np.arange(points)-points//2)*step
    radius_t=np.hypot(b,speed*t)
    weight=np.exp(-.5*(t/duration)**2);weight/=weight.sum()
    freq=2*pi*np.fft.fftfreq(points,step)
    rows=[]
    for width,kind in ((.3,"thin"),(1.3,"thick")):
        shift=np.zeros_like(t)
        for n in range(1,19):
            x=n*radius_t/radius
            harmonic=3*new_area/(4*pi*pi)*(32*pi*pi*3)*speed**4*np.exp(-x)*(3+3*x+x*x)/(64*radius*radius_t**5)
            shift+=harmonic*(-np.expm1(-(n*width)**2))
        mean=E-float(weight@shift)
        var=1/(4*duration**2)+float(weight@(shift-(weight@shift))**2)
        f=E-shift
        phase=np.r_[0.,np.cumsum((f[:-1]+f[1:])*step/2)]
        spectrum=np.abs(np.fft.fft(np.sqrt(weight)*np.exp(1j*phase)))**2/points
        # Split the zero-frequency bin equally between the two half-lines.
        wrong=float(spectrum[freq<0 if kind=="thin" else freq>0].sum()+spectrum[0]/2)
        assert abs(float(spectrum@freq)-mean)<4e-8
        assert abs(float(spectrum@(freq-mean)**2)-var)<max(1e-11,var*2e-6)
        upper=var/(var+mean**2)
        rows.append(dict(kind=kind,mean=mean,sd=sqrt(var),cantelli=upper,fft_wrong=wrong))
    return dict(area=new_area,speed=speed,clock_duration=duration,incident_mode=n_mode,energy=E,results=rows)


def receipt_bounds():
    j,J,phase,mass,charge=kernel()
    angles=2*pi*np.arange(4096)/4096
    def visibility(harmonics):
        amps=np.abs(np.fft.fft(np.exp(1j*(harmonics@np.cos(np.outer(j,angles)))))/len(angles))
        weight=amps[0]**2+amps[1]**2
        return float(2*amps[0]*amps[1]/weight),float(weight)
    near,accepted=visibility(phase)
    far,far_accepted=visibility(kernel(b=160.)[2])
    mode=180*4*pi/sqrt(2e12)
    bound_a=1.2*float(J@(j*j))/mode*(4/near**2-1)/20000
    bound_b=10*far**2/(1-mode/(.8*J[0]))
    # Deterministic quantiles of one Born angular distribution (no Monte Carlo).
    # The separate probability inequalities in the text do not rely on these samples.
    grid=2*pi*np.arange(500)/500
    prob=(1+near*np.cos(grid))/len(grid)
    cumulative=prob.cumsum()
    sample=grid[np.searchsorted(cumulative,(np.arange(1000)+.5)/1000)]
    loglik=np.log1p(near*np.cos(sample[:,None]-grid[None,:])).sum(axis=0)
    posterior=np.exp(loglik-np.max(loglik));posterior/=posterior.sum()
    return dict(near_visibility=near,near_accepted_fraction=accepted,far_visibility=far,
                far_accepted_fraction=far_accepted,incident_energy=mode,
                near_count=20000,far_count=10,thin_failure_upper=bound_a,thick_failure_upper=bound_b,
                representative_posterior_first_variance=float(1-abs(posterior@np.exp(1j*grid))**2))


def radiation_code():
    # xxyy orbit and xyxy orbit. Digits refer to charges or mode labels.
    orbits=[[0b0011,0b0110,0b1100,0b1001],[0b0101,0b1010]]
    code=np.zeros((16,2),complex)
    for column,indices in enumerate(orbits):
        code[indices,column]=1/sqrt(len(indices))
    errors=[]
    for site in range(4):
        local=np.moveaxis(code.reshape(2,2,2,2,2),site,0).reshape(2,8,2)
        for a in range(2):
            for b in range(2):
                reduced=local[:,:,a]@local[:,:,b].conj().T
                errors.append(float(np.max(np.abs(reduced-(np.eye(2)/2 if a==b else 0)))))
    assert max(errors)<3e-15
    # Probability of fewer than k suitable slots among m independent quadruples.
    p=.1; prob=6*p*p*(1-p)**2; m=600;k=10
    fail=sum(comb(m,i)*prob**i*(1-prob)**(m-i) for i in range(k))
    return dict(single_packet_kl_error=max(errors),type_probability=prob,
                eligible_quartets=m,encoded_qubits=k,insufficient_probability=fail)


def falling():
    integral=quad(lambda angle:2*np.sin(angle)**2,0,pi/2)[0]
    assert abs(integral-pi/2)<1e-14
    cases=[]
    for e,l in ((1.,0.),(1.5,0.),(1.,2.),(.8,3.)):
        val=quad(lambda r:1/sqrt(e*e+(1/r-1)*(1+(l/r)**2)),0,1,epsabs=1e-12)[0]
        assert val<=integral
        cases.append([e,l,val])
    return dict(proper_time_bound_per_radius=integral,times=cases,
                curvature_at_fixed_x_scales_as_mass_power=-4)


def microscopic_flags():
    # Spin-half fusion paths with twice the spin as the horizontal coordinate.
    def paths(number_of_pairs,level):
        state=[1]+[0]*level
        for step in range(2*number_of_pairs):
            state=[(state[j-1] if j else 0)+(state[j+1] if j<level else 0)
                   for j in range(level+1)]
        return state[0]
    catalan=lambda n:comb(2*n,n)//(n+1)
    for n in range(1,26):
        assert paths(n,2*n)==catalan(n)
        assert catalan(n+1)//(2*catalan(n))==1
        if n>=9:
            assert catalan(n+2)//(4*catalan(n))==3
        for s in (1,2,3):
            assert paths(n+s,2)//(2**s*paths(n,2))==1
    # Orbits under permutations within each physically distinct material group.
    a,b,k=4,5,4
    possible=set()
    for mask in range(1<<(a+b)):
        if mask.bit_count()==k:
            possible.add((mask% (1<<a)).bit_count())
    assert len(possible)==min(a,k)-max(0,k-b)+1
    return dict(old_pairs=9,full_singlet_dimension=catalan(9),
                one_pair_one_qubit_flags=catalan(10)//(2*catalan(9)),
                two_pairs_two_qubits_flags=catalan(11)//(4*catalan(9)),
                strictly_new_four_puncture_states=catalan(2),
                level_two_three_pairs_three_qubits_flags=paths(12,2)//(8*paths(9,2)),
                equivalent_unmarked_precursors=comb(a+b,k),colored_orbits=len(possible))


def area_records():
    # The old state and the incoming logical state are spectators of the flag.
    old_dim,logical_dim,new_dim=6,2,144
    flags=new_dim//(old_dim*logical_dim)
    omega=np.exp(2j*pi/flags)
    ft=omega**np.outer(np.arange(flags),np.arange(flags))/sqrt(flags)
    click=np.diag([0.]+[1.]*(flags-1))
    initial=ft[:,0]
    tagged=float((initial.conj()@click@initial).real)
    err=float(np.max(np.abs(ft.conj().T@ft-np.eye(flags))))
    assert err<1e-14 and abs(tagged-(1-1/flags))<2e-15
    rng=np.random.default_rng(116)
    v=rng.normal(size=(12000,flags))+1j*rng.normal(size=(12000,flags))
    p0=abs(v[:,0])**2/np.sum(abs(v)**2,axis=1)
    tail=float(np.mean(p0>.25))
    assert abs(tail-.75**(flags-1))<.006
    return dict(old_states=old_dim,logical_states=logical_dim,new_states=new_dim,flag_count=flags,
                unbiased_click=tagged,identity_click=0.,unitarity_error=err,haar_quiet_mean=float(np.mean(p0)),
                haar_quiet_tail=tail,exact_tail=.75**(flags-1),random_seed=116,
                absorbed_entropy_40_log_quiet=np.log(2.)-40)


def ordinary_horizon():
    planck_mass=sqrt(hbar*c/G)
    rho=40.
    geom_frequency=rho**(-1.5)
    heat_occ=1/expm1(16*pi*geom_frequency)
    rows=[]
    for mass_kg in (.001,.01,1.):
        source=mass_kg/planck_mass
        # Independently integrate the squared time derivative of the tidal tensor.
        def tidal_power(angle):
            n=np.array([np.cos(angle),np.sin(angle),0.])
            vel=geom_frequency*np.array([-np.sin(angle),np.cos(angle),0.])
            deriv=-3*source/rho**3*(np.outer(n,vel)+np.outer(vel,n))
            return (16/45)*float(np.sum(deriv**2))
        number=quad(tidal_power,0,2*pi)[0]/(2*geom_frequency**2)
        formula=(32*pi/5)*source**2/rho**6
        assert abs(number/formula-1)<4e-15
        homodyne=.5*erfc(sqrt(number/(2*(2*heat_occ+1))))
        rows.append(dict(mass_kg=mass_kg,horizon_quanta_per_orbit=number,
                         vacuum_no_capture=exp(-number),thermal_read_error=homodyne))
    kerr=[]
    for spin in (.1,.5,.9,.999):
        actual=quad(lambda t:sqrt((1+sqrt(1-spin**2)*np.cos(t))**2+spin**2),0,pi)[0]
        assert actual<pi*(1+spin/2)
        kerr.append([spin,actual,pi*(1+spin/2)])
    return dict(planck_mass_kg=planck_mass,radius_in_gravitational_masses=rho,
                thermal_occupation=heat_occ,circular_sources=rows,kerr_time_in_mass_units=kerr)


def main():
    ensemble=continuum()
    report=dict(continuum=ensemble,exchange=exchange(),receipts=receipt_bounds(),small_contact=finite_contact(1,.1),extended_contact=finite_contact(500,.002),radiation=radiation_code(),falling=falling(),ordinary_horizon=ordinary_horizon(),area_records=area_records(),microscopic_flags=microscopic_flags())
    path=ROOT/"verification"/"continuum-layer-interface-results.json"
    path.write_text(json.dumps(report,indent=2,allow_nan=False)+"\n",encoding="utf8")
    j,eng,phase,mass,charge=kernel()
    sigma=np.linspace(0,1.65,240)
    d=eng@(-np.expm1(-np.outer(j,sigma)**2))
    fig,ax=plt.subplots(figsize=(6.4,3.1),layout="constrained")
    ax.fill_between(sigma,.8*d,1.2*d,color="#83bcc0",alpha=.55,label="20% variation in pair strength")
    ax.plot(sigma,d,color="#18535b",label="Continuum interaction energy")
    ax.axhspan(ensemble["thin_ceiling"],ensemble["thick_floor"],color="#d69a46",alpha=.23,
               label="Incident energies that separate the outcomes")
    ax.axvline(.3,color="0.4",ls=":",lw=1);ax.axvline(1.3,color="0.4",ls=":",lw=1)
    ax.set(xlabel="Width of each material population on the compact circle (rad)",
           ylabel=r"Energy in $\ell_{11}^{-1}$",xlim=(0,1.65),ylim=(0,.0053))
    ax.legend(frameon=False,fontsize=8,loc="upper left")
    out=ROOT/"manuscripts"/"continuum_layer_interface.pdf";out.parent.mkdir(parents=True,exist_ok=True)
    fig.savefig(out,metadata={"CreationDate":None,"ModDate":None});plt.close(fig)
    print("Continuum interaction, integer exchange, radiation isometry and proper time verified.")


if __name__=="__main__":
    main()
