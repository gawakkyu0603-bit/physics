"""Local completion time and available energy of a gravitational receiver."""
from fractions import Fraction
from math import ceil, log, pi, sqrt
from pathlib import Path
import json
import numpy as np
from scipy.constants import c, hbar
from boundary_exchange_recovery import occupation_weights, lapse_series

ROOT=Path(__file__).resolve().parents[1]
LENGTH=1e-4
WAVELENGTH=28.22e-6
PHASE=2*pi*LENGTH/WAVELENGTH
MOBILE=191


def scattering(coupling):
    # For the three (p,q) charges, the dimensionless tensions are measured in T_F units.
    tension=np.array([1.,1/coupling,np.hypot(1,1/coupling)])
    amplitudes=2*np.sqrt(np.outer(tension,tension))/tension.sum()-np.eye(3)
    assert abs(amplitudes.T@amplitudes-np.eye(3)).max()<2e-15
    return tension,float(amplitudes[0,0]**2)


def main():
    integers,den=occupation_weights(MOBILE)
    weights=np.array([n/den for n in integers])
    nodes=np.linspace(-1.,1.,MOBILE+1)
    levels=lapse_series(np.arccos(nodes),4.,.05)
    dif=levels[:,None]-levels[None,:]
    joint=np.outer(weights,weights)
    def bare(length):
        phase=2*pi*length/WAVELENGTH
        return [float(abs(weights@np.exp(-1j*k*phase*(levels-levels[0])))**2) for k in (1,2,3)]
    flights=[]
    for length in (LENGTH,.001,1.7):
        p=bare(length)
        flights.append(dict(length_m=length,neutral=p,smallest_sufficient_count=ceil(log(.01/3)/log(max(p))),
                            binary_error=(1-sqrt(1-p[0]))/2))
    gs=1/32
    tension,r=scattering(gs)
    tau=LENGTH/c
    p=[]
    for k in (1,2,3):
        shift=k*PHASE*dif
        loss=2*np.sin(shift/2)**2
        factor=(1-r)*((1-r)-loss)/((1-r)**2+2*r*loss)
        rational=float((joint*factor).sum())
        direct=sum((1-r)*r**m*abs(weights@np.exp(-1j*(m+1)*k*PHASE*(levels-levels[0])))**2
                   for m in range(600))
        assert abs(rational-direct)<r**600+1e-14
        p.append(rational)
    # Bound valid uniformly in the stated membrane and junction family.  Round
    # constants in the conservative direction and sum each node separation exactly.
    slope=Fraction(6,10000); phase_min=Fraction(222,10); rmin=Fraction(9394,10000)
    rmax=Fraction(97,100)
    assert float(rmin)<=r<scattering(1/64)[1]<float(rmax)
    assert 3*PHASE*.0436<pi
    weights_by_gap=[sum(integers[i]*integers[i+h] for i in range(MOBILE+1-h))*(1 if h==0 else 2)
                    for h in range(MOBILE+1)]
    bound=Fraction(0)
    for h,count in enumerate(weights_by_gap):
        delta=phase_min*slope*Fraction(2*h,MOBILE)
        bound+=Fraction(count,den**2)*(1-rmin)**2/((1-rmin)**2+2*rmin*Fraction(1,5)*delta**2)
    assert bound<Fraction(983,1000)
    trips=int((.3e-9)//tau)
    assert trips>=898
    assert 3*max(p)**8+8*r**trips<.01
    uniform_error=3*.983**384+384*.97**898
    assert uniform_error<.0042
    var_floor=float(slope)**2*(MOBILE+1)/(2*MOBILE)
    uniform_bare=ceil(log(.01/3)/log(1-4/pi**2*PHASE**2*var_floor))
    # Equal geometric lengths L/2, eight independently stored string junctions.
    grain_mass=1.31e-9
    grain_energy=grain_mass*c*c
    ell=LENGTH/2
    needed_length=sqrt(8*ell*tension.sum()*hbar*c/(2*pi*grain_energy))
    single_length=sqrt(ell*hbar*c/(2*pi*grain_energy))
    result=dict(wavelength_m=WAVELENGTH,light_crossing_s=tau,one_pass=flights,
                weak_arm_reflection=r,mean_dwell_s=tau/(1-r),timed_return=p,round_trips_before_deadline=trips,
                eight_probe_error_bound=3*max(p)**8+8*r**trips,uniform_return_bound=float(bound),
                uniform_384_error_bound=uniform_error,uniform_single_pass_probes=uniform_bare,
                eight_junction_minimum_string_length_m=needed_length,single_arm_minimum_string_length_m=single_length)
    (ROOT/'verification'/'gravitational-receipt-transit-results.json').write_text(
        json.dumps(result,indent=2,allow_nan=False)+'\n',encoding='utf8')
    print('Single-pass and timed readout:',flights[0]['smallest_sufficient_count'],result['eight_probe_error_bound'])
    print('Uniform bound and minimum string length:',float(bound),needed_length)


if __name__=='__main__':
    main()
