"""Numerical comparison in the physical units of the archived observables."""
import math
import re

RTOL=3e-5
# These particular observables have analytical value zero. Scales refer to the
# normalized operator or energy used by the corresponding calculation.
ZERO_LIMITS={
    "compact-matrix-radiation.polarization.max_projection_error":(1.,2e-12),
    "compact-matrix-radiation.receipts.sweeps[].symplectic_residual":(1.,8e-10),
    "preterminal-matching.inclusive.coherent_rates.none.ideal.minimum":(16.,2e-13),
    "preterminal-matching.inclusive.coherent_rates.none.gaussian.minimum":(16.,2e-13),
    "cat-sky-geometry.sky_tests.charge_tests.common.opposite_kick_energy_over_one":(1.,2e-13),
    "cat-radius-comparison.cat_contacts.readout_examples[0].mean_momentum_change":(1.,5e-13),
}
# Dimensional resolution in the stated units. A cap relative to a nonzero
# reference prevents even these floors from admitting a spurious physical zero.
UNIT_FLOORS={"fall_time_s":1e-12,"lead_before_horizon_s":1e-12,"advanced_margin_s":1e-12,
             "static_proper_margin_s":1e-12,"balanced_time_s":1e-12,"echo_source_frame_ms":1e-9,
             "separation_m":1e-10,"radius_m":1e-10,"transition_r_squared_m2":1e-34,
             "exchange_per_second":1e-45,"tidal_energy_for_0p1_rad_at_100_Hz_J":1.}

def scalar_ok(expected, actual, path):
    if type(actual) not in (float,int) or not math.isfinite(actual):return False
    category=re.sub(r"\[\d+\]","[]",path)
    residual=ZERO_LIMITS.get(path,ZERO_LIMITS.get(category))
    if residual:
        scale,tol=residual
        return max(abs(expected),abs(actual))/scale <= tol
    if expected==0:
        return actual==0
    if not math.isfinite(expected) or actual==0 or (actual>0)!=(expected>0):return False
    abs_limit=min(UNIT_FLOORS.get(path.rsplit(".",1)[-1],0.),abs(expected)*1e-3)
    return math.isclose(expected,actual,rel_tol=RTOL,abs_tol=abs_limit)

def compare(expected, actual, path):
    if isinstance(expected,dict):
        if not isinstance(actual,dict) or expected.keys()!=actual.keys():raise ValueError("keys at "+path)
        return sum(compare(v,actual[k],path+"."+k) for k,v in expected.items())
    if isinstance(expected,list):
        if not isinstance(actual,list) or len(expected)!=len(actual):raise ValueError("length at "+path)
        return sum(compare(x,y,f"{path}[{i}]") for i,(x,y) in enumerate(zip(expected,actual)))
    if type(expected) is float:
        if not scalar_ok(expected,actual,path):raise ValueError(f"{path}: expected {expected!r}, got {actual!r}")
        return 1
    if type(expected)!=type(actual) or expected!=actual:raise ValueError(f"{path}: expected {expected!r}, got {actual!r}")
    return 0

def regression():
    path="cat-relational-collapse.hydrogen[0].radial_single_displacement"
    reference=5.4817058785941306e-64
    assert scalar_ok(reference,reference*(1+1e-7),path)
    assert all(not scalar_ok(reference,x,path) for x in (0.,1e-7,-reference,float("nan")))
    path="preterminal-matching.inclusive.coherent_rates.none.ideal.minimum"
    assert scalar_ok(-1e-15,1e-15,path) and not scalar_ok(-1e-15,1e-7,path)
    assert not scalar_ok(1e-90,0.,"probe.exchange_per_second")

