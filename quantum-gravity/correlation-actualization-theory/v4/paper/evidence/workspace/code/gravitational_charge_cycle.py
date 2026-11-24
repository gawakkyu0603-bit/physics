"""Checks for a gravitationally driven charge on a material rim (paper 2, Z.11)."""
import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import expm
from scipy.optimize import brentq

ROOT = Path(__file__).resolve().parents[1]
C = 299792458.0
G = 6.67430e-11
HBAR = 1.054571817e-34
KB = 1.380649e-23
GM_SUN = 1.3271244e20
TAU = 2 * math.pi


def close(value, expected, tol=1e-10):
    assert abs(value-expected) <= tol * max(1.0, abs(expected)), (value, expected)


def clock_and_charge():
    rows = []
    for masses in (3, 4e6, 1e9):
        rs = 2 * GM_SUN * masses / C**2
        proper = 2*rs/(3*C) * (3**1.5 - 1.5**1.5)
        margin = 2*rs/(3*C) * (1.5**1.5 - 1)
        advanced = rs/C * quad(lambda x: x/(1+math.sqrt(x)), 1, 1.5)[0]
        close(proper, rs/C*quad(math.sqrt, 1.5, 3)[0])
        assert advanced > margin/2
        for mass, size in ((70.,1.7), (1.31e-9,1.e-4)):
            loop_time = size/C
            y = mass*C*size/HBAR
            static_local_hawking = HBAR*C/(4*math.pi*rs*KB*math.sqrt(1-1/1.5))
            sector_kelvin = TAU*HBAR*C/(size*KB)
            warm_a = sector_kelvin/300
            # Poisson summation at high temperature avoids summing a wide Gaussian.
            theta = math.sqrt(math.pi/warm_a)*sum(math.exp(-math.pi**2*j*j/warm_a)
                                                      for j in range(-10,11))
            def gain(speed):
                return rs/C*quad(lambda x: speed*x/(1+speed*math.sqrt(x)),1,1.5)[0]
            close(gain(1),advanced)
            min_speed=brentq(lambda speed: gain(speed)-2*loop_time,0.,1.,xtol=1e-30)
            assert 2*loop_time < advanced and loop_time < margin
            rows.append(dict(solar_masses=masses, object_kg=mass, rim_length_m=size,
                             geometric_energy_ratio=y, drive_proper_s=proper,
                             remaining_proper_s=margin, remaining_advanced_s=advanced,
                             one_round_trip_s=loop_time, minimal_relative_speed_in_c=min_speed,
                             neutral_pair_energy_J=TAU*HBAR/loop_time,
                             blank_probability_at_300K=1/theta,
                             log_first_sector_relative_weight_at_local_T_H=-sector_kelvin/static_local_hawking))
    return rows


def constraint_slab():
    # Time-symmetric initial metric in areal gauge, G=c=1. Arbitrary mass profile.
    lo, hi = 1.2, 2.3
    def m(r): return .07+.013*r**3+.004*r**2
    def dm(r): return .039*r**2+.008*r
    def rp(r): return math.sqrt(1-2*m(r)/r)
    face = lambda r: 8*math.pi*r*rp(r)
    curvature = quad(lambda r: 4*math.pi*r**2*(2+2*rp(r)**2)/r**2/rp(r), lo, hi)[0]
    receipt = (-2*(face(hi)-face(lo))+curvature)/(16*math.pi)
    material = quad(lambda r: dm(r)/rp(r),lo,hi)[0]
    close(receipt,material)
    # Same core mass but an empty annulus.
    speed = lambda r: math.sqrt(1-.14/r)
    vacuum = (-16*math.pi*(hi*speed(hi)-lo*speed(lo))+
              quad(lambda r: 8*math.pi*(1+speed(r)**2)/speed(r),lo,hi)[0])/(16*math.pi)
    close(vacuum,0)
    return dict(slab_rest_energy=material, curvature_reading=receipt, vacuum_reading=vacuum)


def phase_slope(theta, y):
    # d arg(1+y exp(i theta))/d theta, stable for either side of 1.
    if y > 1:
        inverse = 1/y
        return (1+inverse*np.cos(theta))/(1+inverse**2+2*inverse*np.cos(theta))
    return y*(y+np.cos(theta))/(1+y*y+2*y*np.cos(theta))


def open_loop():
    rows=[]
    for y in (.1,.4,.85,.97,1.03,1.4,3.,30.):
        n=int(y>1)
        rho=min(y,1/y)
        degree=quad(lambda a: phase_slope(a,y),0,TAU,points=[math.pi])[0]/TAU
        power=quad(lambda a: phase_slope(a,y)**2,0,TAU,points=[math.pi])[0]/TAU
        close(degree,n)
        close(power,n*n+rho*rho/(2*(1-rho*rho)))
        rows.append(dict(energy_ratio=y, charge=degree, work_in_2pi_hbar_over_T=power))
    t=np.linspace(0,1,8193)
    varying=[]
    for center,offset in ((.7,.9),(1.5,-1.1),(1.3,.8)):
        y=center+offset*np.cos(math.pi*t)**2
        z=1+y*np.exp(1j*TAU*t)
        degree=np.diff(np.unwrap(np.angle(z))).sum()/TAU
        close(degree,int(center>1))
        varying.append(dict(midpoint_ratio=center,endpoint_ratio=center+offset,degree=degree))
    # Direct time evolution of a massive rotating Dirac doublet.
    sigma_x=np.array([[0.,1.],[1.,0.]])
    sigma_y=np.array([[0.,-1j],[1j,0.]])
    strength=math.pi*math.sqrt(5)/2
    state=np.array([1.,-1.],complex)/math.sqrt(2)
    steps=1800
    for i in range(steps):
        angle=TAU*(i+.5)/steps
        state=expm(-1j*strength*(math.cos(angle)*sigma_x+math.sin(angle)*sigma_y)/steps)@state
    excitation=abs(state.sum()/math.sqrt(2))**2
    close(excitation,4/9,2e-6)
    return dict(constant=rows,varying=varying,massive_excitation=excitation)


def compact_loop(y, duration, smooth, filtered):
    # Time in units of one circuit. A right mover encounters every earlier seam crossing.
    t=np.arange(16384)/16384
    def drive(u):
        x=np.clip(u/duration,0.,1.)
        w=x-np.sin(TAU*x)/TAU if smooth else x
        rate=(1-np.cos(TAU*x) if smooth else 1.)/duration
        rate=rate*((u>=0)&(u<duration))
        return w,TAU*rate*phase_slope(TAU*w,y)
    def lift(u):
        w,_=drive(u)
        ang=TAU*w
        if y>1:
            return ang+np.angle(1+np.exp(-1j*ang)/y)
        return np.angle(1+y*np.exp(1j*ang))
    summed=np.zeros_like(t)
    phase_multiplier=np.ones_like(t,dtype=complex)
    for k in range(-2,math.ceil(duration)+3):
        u=t+k
        summed += (lift(u)-lift(u-1)) if filtered else drive(u)[1]
        if not filtered:
            phase_multiplier*=np.exp(1j*lift(u))
    n=int(y>1)
    if filtered:
        # Integrate the actual new slope including its winding. Constant phase is immaterial.
        phase=np.cumsum(np.r_[0.,(summed[1:]+summed[:-1])/2])/len(t)
        phase_multiplier=np.exp(1j*phase)
        close(float(np.max(abs(summed-TAU*n))),0)
    modes=np.fft.fftfreq(len(t))*len(t)
    weights=abs(np.fft.fft(phase_multiplier)/len(t))**2
    spectral_energy=float(np.dot(modes*modes,weights))
    flow=float(np.dot(modes,weights))
    current_energy=float(np.mean((summed/TAU)**2))
    close(flow,n,1e-7)
    close(spectral_energy,current_energy,1e-7)
    if duration==int(duration) and not smooth and not filtered:
        rho=min(y,1/y)**int(duration)
        close(spectral_energy,n*n+rho*rho/(2*(1-rho*rho)))
    return dict(y=y, duration_in_circuits=duration,smooth=smooth,averaged=filtered,
                charge=flow,energy_in_gap_units=spectral_energy,
                chiral_holes=float(np.dot(np.maximum(-modes,0),weights)),
                sideband_weight=1-float(weights[n]))


def shell_and_discharge():
    k=2/3
    m=4/9
    def H(r): return m*r/k+k/(2*r*r)
    x=1e-4
    H2=(H(1+x)-2*H(1)+H(1-x))/x**2
    close(H(1),1)
    close(H2,2,1.e-6)
    lapse=math.sqrt(1-2*m)
    close((1-lapse)/(4*lapse),.5)
    # Proper surface oscillator energy permits precisely the vacuum after a positive-energy single flip.
    shell=[]
    for n in range(1,7):
        sum_mode_energies=2*sum(j+.5 for j in range(n))
        close(sum_mode_energies,n*n)
        shell.append(dict(n=n,minimum_pair_energy=sum_mode_energies,
                          available_neutral_quanta_after_one_flip=n*n-(n-1)**2))
    integral=quad(lambda x:x**5*(1-x)**5,0,1)[0]
    close(integral,1/2772)
    return dict(shell_radius_squared_over_k=1.5, compactness=2*m,lapse=lapse,
                growth_in_c_over_R=math.sqrt(H2),sector_energy=shell,
                energy_fraction_integral=integral)


def packing_and_stability():
    # The normalized shell energy follows surface conservation for a linear local barotrope.
    radial=[]
    for sound_squared in (0.,.5,1.,1.5,2.):
        def h_at(r):
            density_ratio=(1.5*r**(-2*(1+sound_squared))+sound_squared-.5)/(1+sound_squared)
            energy=2*r*r*density_ratio/3
            return (4/9)/energy+energy/(2*r)
        dx=.0001
        h2=(h_at(1+dx)-2*h_at(1)+h_at(1-dx))/dx**2
        close(h2,3-2*sound_squared,2e-6)
        radial.append(dict(dp_dsigma=sound_squared,radial_H_second=h2))
    rng=np.random.default_rng(127)
    gaps=[]
    for count in (4,10,100,1000):
        f=rng.uniform(.3,1.,count)
        f *= min(1.,2/np.linalg.norm(f))
        total=float(np.sum(1/f))
        assert total>=count**1.5/2
        gaps.append(dict(number_of_caps=count,area_proxy=float(np.dot(f,f)),cost=total,
                         lower_bound=count**1.5/2))
    # Inflow at level two. A monopole and opposite rim flip must cancel under all angles.
    angles=np.linspace(0.,TAU,4096,endpoint=False)
    allowed=[]
    for charge in (-2,0,2):
        for magnetic_event in (-1,0,1):
            weight=np.mean(np.exp(1j*(charge-2*magnetic_event)*angles))
            close(abs(weight),int(charge==2*magnetic_event))
            if abs(weight)>.5:
                allowed.append([charge,magnetic_event])
    return dict(radial=radial,caps=gaps,minimum_radius_for_trillion_caps_in_planck_units=1e9/math.sqrt(2),
                gauge_invariant_endpoint_pairs=allowed)


def source_and_lifetime():
    # A scalar curvature pair at a heavy, localized four-dimensional receiver.
    # Mode density and two derivatives give omega^5 d omega per polarization.
    scaled = []
    for gap in (.25, 1., 3.):
        width = quad(lambda w: w**5*(gap-w)**5,0,gap)[0]
        close(width,gap**11/2772)
        scaled.append(dict(gap=gap,rate_without_matrix_element=width))
    intervals=[]
    # R and time in Planck units. Factor out the unknown microscopic prefactor and lapse.
    for ri,rf in ((1e6,1e3),(1e3,10.),(100.,2.)):
        depth=quad(lambda log_r: math.exp(-2*log_r),math.log(rf),math.log(ri))[0]
        close(depth,(rf**-2-ri**-2)/2)
        intervals.append(dict(initial_radius_in_planck_lengths=ri,final_radius_in_planck_lengths=rf,
                              depth_divided_by_rate_to_shrinkage_coefficient=depth))
    # Independent quantum-channel calculation with a reference qubit and an orthogonal failure flag.
    strength=.83
    survival=math.exp(-strength)
    target=np.array([1,0,0,1],complex)/math.sqrt(2)
    pair=np.outer(target,target.conj())
    recovered=(1-survival)*pair+survival*np.eye(4)/4
    close(float(np.vdot(target,recovered@target).real),1-3*survival/4)
    radii=[1.1,1.5,3.,12.]
    for r in radii:
        invariant=12/r**6
        gradient_sq=(1-1/r)*(-6*invariant/r)**2
        local_compactness=1/(1+gradient_sq/(6*math.sqrt(3)*invariant**2.5))
        close(local_compactness,1/r)
    return dict(spectrum=scaled,intervals=intervals,
                conditional_decay_test_entanglement_fidelity=float(np.vdot(target,recovered@target).real),
                compactness_checked_at_radii=radii)


def radiating_shell():
    # Geometrized radius, retarded time and proper time; initial radius equals one.
    # Integrate the junction dynamics with its charge loss, rather than inserting m(u).
    solutions=[]
    for speed in (.025,.2,.48):
        beta=math.sqrt(1+speed*speed)
        q=2*(beta-2*speed)/3
        doppler=(beta+speed)/3
        compactness=2*beta*q-q*q
        analytic_luminosity=compactness*speed*doppler/2
        def rhs(t,state):
            R,v,k,m,u=state
            root=math.sqrt(1+v*v)
            z=root-k/(R*R)+v
            # Continuous population leaves at the instantaneous rate needed for this branch.
            dk=-2*q*speed*R
            return (v,root*(dk/k+root/R-1.5*k/R**3),dk,dk/R*z,1/z)
        # Close to the algebraic branch the radial mode grows, so compare away from the singular end.
        final=.55/speed if speed>.1 else .12/speed
        sol=solve_ivp(rhs,[0,final],[1.,-speed,q,compactness/2,0.],
                      t_eval=np.linspace(0,final,101),rtol=2e-11,atol=2e-13,method="DOP853")
        assert sol.success
        R,v,k,m,u=sol.y
        error=float(max(np.max(abs(R-(1-speed*sol.t))),np.max(abs(m-compactness*R/2)),
                        np.max(abs(k-q*R**2)),np.max(abs(v+speed))))
        assert error<2e-7,error
        close(float(m[0]-m[-1]),float(analytic_luminosity*(u[-1]-u[0])),2e-7)
        solutions.append(dict(inward_speed=speed,charge_per_area=q,compactness=compactness,
                              frequency_factor=doppler,Bondi_luminosity=analytic_luminosity,
                              proper_lifetime_in_initial_radii=1/speed,
                              retarded_lifetime_in_initial_radii=1/(speed*doppler),
                              integration_duration=final,maximum_junction_error=error))
    # Fixed lapse and dense, disjoint equal loops. Ignore order-one angular and greybody factors.
    rates=[]
    q=2/3
    z=1/3
    for radius in (1e3,1e6,1e9):
        x=1/radius**2
        f=(4*x/q)**(1/3)
        sites=q*f/x
        maxsites=4/(f*f)
        close(sites,maxsites)
        power=q*z*z*x*x/f**5
        corrected=power*f*f
        close(corrected/x,(q*z)**2/4)
        rates.append(dict(radius_in_planck_units=radius,angular_rim_fraction=f,occupied_sites=sites,
                          bare_power_over_inverse_area=power/x,curvature_vertex_power_over_inverse_area=corrected/x,
                          one_pair_minimum_hard_frequency_times_radius=z/(2*f)))
    return dict(solutions=solutions,packed_rates=rates)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,default=ROOT/"verification"/"gravitational-charge-cycle-results.json")
    out=parser.parse_args().output
    ring=[compact_loop(y,T,s,filtered) for y,T,s in
          ((1.4,1.,False),(1.4,2.,False),(1.4,4.,False),
           (.7,1.35,True),(1.4,1.35,True),(3.1,.72,True))
          for filtered in (False,True)]
    result=dict(clock=clock_and_charge(),slab=constraint_slab(),cycle=open_loop(),
                ring=ring,discharge=shell_and_discharge(),lifetime=source_and_lifetime(),packing=packing_and_stability(),radiation=radiating_shell())
    out.write_text(json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf-8")
    print(out.name)


if __name__=="__main__":
    main()
