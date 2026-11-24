"""Relational matrix cosmology, directional Pantheon+ expansion, and CAT receiver tests."""
import json
from math import factorial, pi
from pathlib import Path

import numpy as np
from scipy import constants, linalg, optimize
from scipy.integrate import solve_ivp
from scipy.stats import chi2, poisson

ROOT = Path(__file__).resolve().parents[1]


def generators(j):
    m = np.arange(j,-j-1,-1)
    up = np.diag(np.sqrt((j-m[1:])*(j+m[1:]+1)), 1)
    return np.array([(up+up.T)/2,(up-up.T)/2.0j,np.diag(m)])


def bracket(a,b):
    return a@b-b@a


def geometry():
    """Check the exact block kernel and independently read the radial and angular speeds."""
    def ode(t, state):
        a, da = state
        return [da, -2*a**3]
    sol = solve_ivp(ode, (0,1.6), [.6,.7],method="DOP853",dense_output=True,
                    rtol=3e-13,atol=3e-15,max_step=.04)
    assert sol.success
    t = .55
    a, da = sol.sol(t)
    energy = .6**4+.7**2
    c = .8
    speed = np.hypot(c,da)
    speed_derivative = -2*a**3*da/speed
    lapse = a*np.sqrt(speed)
    radial_h = (da/a - speed_derivative/(2*speed))/lapse
    angular_h = speed_derivative/(2*speed*lapse)
    q = a**4/(c*c+energy)
    np.testing.assert_allclose(angular_h,-q*radial_h,atol=2e-13)
    def scale(tt):
        aa, ad = sol.sol(tt)
        cc = np.hypot(c,ad)
        return np.array([aa/np.sqrt(cc),np.sqrt(cc)])
    step = 1e-5
    derivative = (np.log(scale(t+step))-np.log(scale(t-step)))/(2*step*lapse)
    np.testing.assert_allclose(derivative,[radial_h,angular_h],atol=2e-9)
    records = []
    ell, p = 2, .7
    continuum = speed**2*p**2 + a**2*ell*(ell+1)
    for j in (2,4,8,16,32):
        spin = generators(j)
        casimir = j*(j+1)
        k = p/np.sqrt(casimir)
        plus = sol.sol(t+k/2)[0]
        minus = sol.sol(t-k/2)[0]
        eig = (c*p)**2 + casimir*(plus-minus)**2 + plus*minus*ell*(ell+1)
        # Highest spherical tensor in the adjoint spin-ell representation.
        probe = np.linalg.matrix_power(spin[0]+1j*spin[1],ell)
        probe /= np.linalg.norm(probe)
        direct = (c*p)**2*probe
        for jj in spin:
            first = plus*jj@probe-minus*probe@jj
            direct += plus*jj@first-minus*first@jj
        np.testing.assert_allclose(direct,eig*probe,atol=2e-12)
        for jj in spin:
            np.testing.assert_allclose(sum(bracket(mm,bracket(mm,jj)) for mm in spin),
                                       2*jj, atol=3e-12)
        records.append([j,eig,abs(eig-continuum)])
    assert records[-1][2]<records[0][2]/100
    # Reconstruct the densitized inverse metric in a local unit angular frame.
    metric = np.diag([-a*a*speed,a*a/speed,speed,speed])
    kinetic = np.sqrt(-np.linalg.det(metric))*np.linalg.inv(metric)
    np.testing.assert_allclose(kinetic,np.diag([-1.,speed**2,a*a,a*a]),atol=4e-14)
    # Use proper time and the recovered R_{0i0i} to drive an ordinary, small
    # quadrupole oscillator. The coupling and frequency characterize this probe.
    def tide_rhs(tt, state):
        aa, vv = sol.sol(tt)
        acc = -2*aa**3
        cc = np.hypot(c,vv)
        cp = vv*acc/cc
        cpp = (acc**2-6*aa**2*vv**2-cp**2)/cc
        rate_c = cp/cc
        drate_c = cpp/cc-rate_c**2
        dlog = np.array([vv/aa-rate_c/2, rate_c/2])
        ddlog = np.array([acc/aa-(vv/aa)**2-drate_c/2, drate_c/2])
        nn = aa*np.sqrt(cc)
        tide = -(ddlog + dlog**2 - (vv/aa+rate_c/2)*dlog)/nn**2
        tau = state[0]
        amplitude = nn*(tide[0]-tide[1])*np.exp(1j*3*tau)
        return [nn,amplitude.real,amplitude.imag]
    period = (.15,.70)
    pulse = solve_ivp(tide_rhs,period,[0.,0.,0.],rtol=8e-12,atol=1e-13)
    assert pulse.success
    duration, x, y = pulse.y[:,-1]
    # Reparametrize the same material clock by s=exp(tau_matrix).
    def relabel(s, state):
        return np.asarray(tide_rhs(np.log(s),state))/s
    other = solve_ivp(relabel,np.exp(period),[0.,0.,0.],rtol=8e-12,atol=1e-13)
    assert other.success
    np.testing.assert_allclose(other.y[:,-1],pulse.y[:,-1],atol=3e-11)
    unit_drive = x*x+y*y
    # The local Weyl count uses the frozen, low-offset scalar symbol. Do not
    # extrapolate the symbol beyond the band in which the exact kernel is local.
    def spatial_count(cut):
        angular = np.arange(int(cut/a)+1)
        return np.sum((2*angular+1)*np.sqrt(np.maximum(0.,cut**2-a*a*angular*(angular+1))))/(np.pi*speed)
    slopes = [[cut,float(np.log2(spatial_count(2*cut)/spatial_count(cut)))] for cut in (.2,20.,80.)]
    assert abs(slopes[-1][1]-3)<.01 and abs(slopes[0][1]-1)<1e-12
    # A pair of rotating SU(2) triplets tests the mixed radial/angular case.
    def rotor(tt,state):
        pos,vel = state[:2],state[2:]
        return np.r_[vel,-2*(pos@pos)*pos]
    initial = np.array([.6,0.,.3,.58])
    rot = solve_ivp(rotor,(0.,.65),initial,rtol=4e-12,atol=2e-14,dense_output=True)
    pos,vel=np.split(rot.sol(t),2)
    radius = np.linalg.norm(pos)
    rc = np.sqrt(c*c+vel@vel)
    radial_velocity = (pos@vel)/radius
    angular_momentum = pos[0]*vel[1]-pos[1]*vel[0]
    c_der = -2*radius**3*radial_velocity/rc
    rr_lapse = radius*np.sqrt(rc)
    h2 = np.array([radial_velocity/radius-c_der/(2*rc),c_der/(2*rc)])/rr_lapse
    re = (initial[2:]@initial[2:])+(initial[:2]@initial[:2])**2
    np.testing.assert_allclose([vel@vel+radius**4,angular_momentum,h2[1]],
                               [re,.6*.58,-radius**4*h2[0]/(c*c+re)],atol=4e-11)
    return dict(t=t,a=float(a),a_prime=float(da),longitudinal_speed=float(speed),
                matter_clock=dict(proper_duration=float(duration),omega=3.,
                                  unit_drive_occupation=float(unit_drive),
                                  unit_probe_excitation=float(-np.expm1(-unit_drive))),
                spatial_count_slopes=slopes,
                rotating_triplets=dict(angular_momentum=float(angular_momentum),H_parallel=float(h2[0]),
                                       H_sphere=float(h2[1])),
                H_parallel=float(radial_h),H_sphere=float(angular_h),q=float(q),
                limiting_frequency_squared=float(continuum),finite_spin=records)


def landscape():
    """Compare invariant orbital area ratios with direct matrix trajectories."""
    energy, angular_momentum = 1.+.65**2,.65
    eta = angular_momentum**2/energy**1.5
    roots = sorted(float(z.real) for z in np.roots([1.,0.,-1.,eta]) if z.real>0 and abs(z.imag)<1e-13)
    lower,upper = roots
    def rhs(t,state):
        pos=state[:2]
        return np.r_[state[2:],-2*np.dot(pos,pos)*pos]
    def turning(t,state):
        return np.dot(state[:2],state[2:])
    sol = solve_ivp(rhs,(0.,3.),[1.,0.,0.,.65],events=turning,method="DOP853",
                    rtol=5e-13,atol=1e-14,max_step=.04)
    extrema = sol.y_events[0]
    assert len(extrema)>=3
    ratios = []
    for s in (.1,.5,1.,2.,10.):
        ratio = np.sqrt((1+s-lower**2)/(1+s-upper**2))
        area_over_4pi = np.sqrt(s*energy+np.sum(extrema[:,2:]**2,axis=1))
        direct = float(area_over_4pi.max()/area_over_4pi.min())
        np.testing.assert_allclose(ratio,direct,atol=4e-12)
        ratios.append([s,float(ratio),direct])
    assert all(first[1]>second[1] for first,second in zip(ratios,ratios[1:]))
    # Pick turning radii squared 1/2 and 1. These simple roots give an
    # analytic continuum even after coordinate and unit changes are removed.
    exact = solve_ivp(rhs,(0.,3.),np.array([1.,0.,0.,np.sqrt(3)/2]),events=turning,
                      method="DOP853",rtol=5e-13,atol=1e-14,max_step=.04)
    points = exact.y_events[0]
    np.testing.assert_allclose(np.sum(points[:3,:2]**2,axis=1),[1.,.5,1.],atol=3e-12)
    area_witness=[]
    for slope_squared in (.25,.75,2.25):
        areas = np.sqrt(slope_squared+np.sum(points[:,2:]**2,axis=1))
        direct = float(areas.max()/areas.min())
        ratio = np.sqrt((slope_squared+1.5)/(slope_squared+.75))
        np.testing.assert_allclose(direct,ratio,atol=3e-12)
        area_witness.append([slope_squared,float(ratio),direct])
    # Hold longitudinal flux and energy fixed while changing only the state
    # of the triplets. Compare actual extrema with the invariant cubic.
    fixed_flux = []
    for spin_charge in (.05,.15,.25,.35):
        yy = sorted(z.real for z in np.roots([1.,0.,-1.,spin_charge])
                    if z.real>0 and abs(z.imag)<1e-13)
        rmax = np.sqrt(yy[1])
        orbit = solve_ivp(rhs,(0.,4.),np.array([rmax,0.,0.,np.sqrt(spin_charge)/rmax]),
                          events=turning,method="DOP853",rtol=7e-13,atol=1e-14,max_step=.04)
        pts = orbit.y_events[0]
        assert len(pts)>=3
        velocity_sq = np.sum(pts[:,2:]**2,axis=1)
        area = np.sqrt(.8+velocity_sq)
        expected = np.sqrt((1.8-yy[0]**2)/(1.8-yy[1]**2))
        np.testing.assert_allclose(area.max()/area.min(),expected,atol=4e-12)
        fixed_flux.append([spin_charge,float(expected)])
    assert all(left[1]>right[1] for left,right in zip(fixed_flux,fixed_flux[1:]))
    return dict(L2_over_E32=eta,turning_roots=roots,area_ratios=ratios,
                fixed_energy_one_flux_squared_0p8=fixed_flux,
                exact_area_witness=area_witness,
                circular_radial_over_rotation=np.sqrt(6.),
                max_L2_over_E32=2/(3*np.sqrt(3.)))


def periodic_propagation():
    """Evolve two independent scalar solutions through one radial period."""
    def background(t,state):
        u,v = state[:2],state[2:]
        return np.r_[v,-2*np.dot(u,u)*u]
    def maximum(t,state):
        return np.dot(state[:2],state[2:])
    maximum.direction = -1
    rot = solve_ivp(background,(0.,10.),[1.,0.,0.,.65],events=maximum,
                    method="DOP853",dense_output=True,rtol=8e-13,atol=2e-14,max_step=.06)
    period = float(next(t for t in rot.t_events[0] if t>1e-4))
    def u(t):
        pos = rot.sol(abs(t))[:2]
        return pos if t>=0 else pos*np.array([1.,-1.])
    def monodromy(ell,p,j):
        casimir = j*(j+1)
        k = p/np.sqrt(casimir)
        def rhs(t,state):
            plus,minus = u(t+k/2),u(t-k/2)
            squared = (.8*p)**2 + casimir*np.dot(plus-minus,plus-minus) + np.dot(plus,minus)*ell*(ell+1)
            a,da,b,db = state
            return [da,-squared*a,db,-squared*b]
        run = solve_ivp(rhs,(0.,period),[1.,0.,0.,1.],method="DOP853",rtol=8e-12,atol=1e-13)
        assert run.success
        matrix = run.y[:,-1].reshape(2,2).T
        determinant = float(np.linalg.det(matrix))
        np.testing.assert_allclose(determinant,1.,atol=6e-10)
        halftrace = float(np.trace(matrix)/2)
        return dict(spin=j,ell=ell,p=p,half_trace=halftrace,
                    log_growth_per_period=float(np.arccosh(max(1.,abs(halftrace)))),det=determinant)
    scan=[monodromy(ell,float(p),16) for ell in (0,1,2) for p in np.linspace(.15,3.,20)]
    strongest=max(scan,key=lambda row:row["log_growth_per_period"])
    records=[monodromy(strongest["ell"],strongest["p"],spin) for spin in (8,32,64)]
    assert strongest["log_growth_per_period"]>.04
    return dict(radial_period=period,initial=[1.,0.,0.,.65],longitudinal_slope=.8,
                grid=dict(ell=[0,1,2],p_min=.15,p_max=3.,steps=20),
                samples_tested=len(scan),maximum_on_grid=strongest,
                same_mode_at_other_spins=records,stable_example=scan[0])


def geometry_in_a_material_record():
    """Compare two matrix preparations with the same proper-time readout."""
    duration, frequency, element = .3, 3., .25
    histories = []
    for init in ((.6,.7),(1.2,.1)):
        def rhs(tau,state):
            a,v,_,_ = state
            speed = np.hypot(.8,v)
            acc = -2*a**3
            cp = v*acc/speed
            cpp = (acc**2-6*a**2*v**2-cp**2)/speed
            rate = cp/speed
            drate = cpp/speed-rate**2
            lapse = a*np.sqrt(speed)
            radial, angular = v/a-rate/2, rate/2
            curvediff = -((acc/a-(v/a)**2-drate) + radial**2-angular**2
                         -(v/a+rate/2)*(radial-angular))/lapse**2
            drive = element*curvediff*np.exp(1j*frequency*tau)
            return [v/lapse,acc/lapse,drive.real,drive.imag]
        pulse = solve_ivp(rhs,(0.,duration),[*init,0.,0.],rtol=2e-12,atol=2e-14)
        assert pulse.success
        a,v,x,y = pulse.y[:,-1]
        speed = np.hypot(.8,v)
        mean = x*x+y*y
        histories.append(dict(initial=list(init),longitudinal_speed=float(speed),
                              mean_quanta=float(mean),occupied=float(-np.expm1(-mean))))
    occupied = np.array([h["occupied"] for h in histories])
    weights = np.full(2,.5)
    probability = weights@occupied
    after_yes = weights*occupied/probability
    after_no = weights*(1-occupied)/(1-probability)
    np.testing.assert_allclose(probability*after_yes+(1-probability)*after_no,weights,atol=1e-14)
    return dict(proper_duration=duration,frequency=frequency,quadrupole_matrix_element=element,
                histories=histories,born_yes=float(probability),weights_if_yes=after_yes.tolist(),
                weights_if_no=after_no.tolist(),weights_without_receipt=weights.tolist())


def sky_fit(sample, field="zHD", low=.025, high=.08, first_only=False):
    z = sample[field]
    keep = np.flatnonzero((z>low)&(z<high))
    if first_only:
        _, first = np.unique(sample["CID"][keep],return_index=True)
        keep = keep[np.sort(first)]
    ra,dec = np.deg2rad(sample["RA"][keep]), np.deg2rad(sample["DEC"][keep])
    nx,ny,nz = np.cos(dec)*np.cos(ra),np.cos(dec)*np.sin(ra),np.sin(dec)
    z = z[keep]
    design = np.column_stack([np.ones(len(z)),z-.05,nx,ny,nz,
                              nx**2-nz**2,ny**2-nz**2,2*nx*ny,2*nx*nz,2*ny*nz])
    # An arbitrary magnitude origin only sets the multiplicative expansion unit.
    offset = 17+5*np.log10(z/.05*(1+sample["zHEL"][keep])/(1+z))
    data = sample["m_b_corr"][keep]
    chol = linalg.cholesky(sample["cov"][np.ix_(keep,keep)],lower=True)
    def whiten(vec):
        return linalg.solve_triangular(chol,vec,lower=True,check_finite=False)
    def residual(par):
        return whiten(offset-5*np.log10(design@par)-data)
    def jacobian(par):
        return whiten(-(5/np.log(10))*design/(design@par)[:,None])
    start = np.zeros(design.shape[1])
    start[0] = np.median(10**((offset-data)/5))
    fit = optimize.least_squares(residual,start,jac=jacobian,ftol=1e-12,
                                 gtol=1e-11,xtol=1e-11)
    assert fit.success and np.all(design@fit.x>0)
    covariance = np.linalg.inv(fit.jac.T@fit.jac)
    def relative_eigenvalues(par):
        amp, ax, ay, xy, xz, yz = par[...,0],par[...,5],par[...,6],par[...,7],par[...,8],par[...,9]
        tensor = np.stack([amp+ax,xy,xz, xy,amp+ay,yz, xz,yz,amp-ax-ay],axis=-1)
        return np.linalg.eigvalsh(tensor.reshape(par.shape[:-1]+(3,3)))/amp[...,None]
    values = relative_eigenvalues(fit.x)
    # Joint 95% Gaussian ellipsoid for the six relevant (marginalized) parameters.
    which = [0,5,6,7,8,9]
    subcov = covariance[np.ix_(which,which)]
    # H(n) = coeff dot (A,Qxx,Qyy,Qxy,Qxz,Qyz). The norm of the five Q
    # coefficients never exceeds sqrt(2), by the traceless-tensor identity.
    radius = np.sqrt(chi2.ppf(.95,len(which)))
    delta_H = radius*np.sqrt(3*np.linalg.eigvalsh(subcov)[-1])
    amp = fit.x[0]
    lower_absolute = amp*values[0]-delta_H
    upper_amp = amp+radius*np.sqrt(covariance[0,0])
    return dict(frame=field,low=low,high=high,first_per_source=first_only,
                rows=len(z),distinct_sources=len(np.unique(sample["CID"][keep])),parameters=fit.x.tolist(),
                eigenvalues_over_monopole=values.tolist(),
                local_95_lower_minimum_over_monopole=float(lower_absolute/upper_amp),
                chi2=float(2*fit.cost),dof=len(z)-len(fit.x),
                sample_cov_condition=float(np.linalg.cond(chol)**2))


def readout_tests():
    ns = np.log(2.)
    weights = poisson.pmf(np.arange(50),ns)
    tested = {}
    for name,charge in [("number",lambda m:m),("parity",lambda m:m%2),
                        ("empty",lambda m:int(m!=0)),("common",lambda m:0)]:
        gains = [sum(w for m,w in enumerate(weights) if charge(m)==charge(m+h)) for h in (1,2)]
        tested[name] = dict(dipole=float(gains[0]),quadratic=float(gains[1]),
                            opposite_kick_energy_over_one=float(2*(1-gains[0])))
    np.testing.assert_allclose([tested["empty"]["dipole"],tested["parity"]["quadratic"]],[.5,1.])
    kicks = []
    for r,q,phi in ((.9,1.,0.),(.9,0.,0.),(.9,.5,0.),(.9,1.,pi),(.9,0.,pi)):
        lam=r*np.exp(1j*phi)
        mean=0j
        energy=0.
        for _ in range(1400):
            energy = r**2*energy + 1+2*np.real(lam*q*mean)
            mean = 1+lam*q*mean
        exact=(1-(r*q)**2)/((1-r*r)*abs(1-lam*q)**2)
        np.testing.assert_allclose(energy,exact,atol=3e-12)
        kicks.append([r,q,phi,float(exact)])
    # Number-diagonal histories and a coherent control have the same line
    # strength after averaging the phase origin in a symmetrized auto spectrum.
    N = 30
    k = np.arange(N)
    annih = np.diag(np.sqrt(k[1:]),1).astype(complex)
    vec = np.array([np.exp(-ns/2)*ns**(m/2)/np.sqrt(float(factorial(m))) for m in k])
    rho = np.outer(vec,vec)
    prefix = np.diag(np.diag(rho))
    pair = annih@annih
    auto = pair@pair.conj().T+pair.conj().T@pair
    np.testing.assert_allclose(np.trace(rho@auto),np.trace(prefix@auto),atol=1e-12)
    np.testing.assert_allclose(np.trace(prefix@pair),0.,atol=1e-12)
    np.testing.assert_allclose(np.trace(rho@pair),ns,atol=1e-12)
    # A finite check of the two-mode squeezed, vacuum/occupied reading.
    rr=.8
    n=np.arange(240)
    squeezed_gain=float(np.sum((n[1:]+1)*(1-rr)**2*rr**n[1:]))
    np.testing.assert_allclose(squeezed_gain,1-(1-rr)**2,atol=2e-14)
    chirp_time=1.22*4.92549095e-6
    f=100.
    flux=32/5*constants.c**5/constants.G*(pi*chirp_time*f)**(10/3)
    return dict(occupation=ns,charge_tests=tested,tidally_forced_energies=kicks,
                squeezed_binary_gain=squeezed_gain,phase_averaged_line_weight=float(np.trace(rho@auto).real),
                tidal_energy_for_0p1_rad_at_100_Hz_J=float(.1*flux/(2*pi*f)),
                helicity_write_upper_at_polarization_lower_edge=[1-(.217-.017),1-(.85-.15)],
                FRB_fringe_ratio_one_quarter=.8, distance_ratio_for_10pct_flux_loss=float(1/np.sqrt(.9)))


def radial_bao():
    """A constant coasting H(z)/(1+z) makes every redshift bin measure the same scale."""
    rows = {}
    for line in (ROOT/"data/desi-dr2-bao-table-iv.txt").read_text("utf8").splitlines():
        if not line or line.startswith("#"):
            continue
        fields = line.split()
        if len(fields)==7:
            z,_,_,dh,err,_ = map(float, fields[1:])
            rows[fields[0]] = [z,(1+z)*dh,(1+z)*err]
    _,first,err1 = rows["LRG3+ELG1"]
    _,last,err2 = rows["Lya"]
    return dict(radial_bins=rows, contrast=first-last,
                conservative_sigma=(first-last)/(err1+err2))


def main():
    with np.load(ROOT/"data/cat-pantheonplus-local.npz",allow_pickle=False) as sample:
        fits=[sky_fit(sample), sky_fit(sample,"zCMB"), sky_fit(sample,low=.035),
              sky_fit(sample,first_only=True)]
    result=dict(matrix=geometry(),landscape=landscape(),periodic_propagation=periodic_propagation(),
                material_geometry=geometry_in_a_material_record(),
                pantheon_local=fits,bao=radial_bao(),sky_tests=readout_tests())
    (ROOT/"verification/cat-sky-geometry-results.json").write_text(
        json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf8")
    print("Checked the matrix kernel, cosmological clocks, four full-covariance sky fits and material readouts.")


if __name__=="__main__":
    main()
