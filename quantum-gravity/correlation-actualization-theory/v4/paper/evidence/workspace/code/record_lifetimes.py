"""Check private-record survival, conditional mass conservation, and the RIT flux reduction."""
import json
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from scipy.integrate import quad
from scipy.linalg import expm
from scipy.stats import unitary_group
from scipy.special import spherical_jn

ROOT = Path(__file__).resolve().parents[1]
KMS = 299792.458


def record_channel():
    # Explicit erasure instrument on a pre-existing neutral letter entangled with matter.
    rng = np.random.default_rng(884219)
    psi = rng.normal(size=6) + 1j*rng.normal(size=6)
    psi /= np.linalg.norm(psi)
    rho = np.outer(psi, psi.conj())
    def marginal(x):
        return np.trace(x.reshape(2,3,2,3),axis1=1,axis2=3)
    for s in (0.,.17,.61,1.):
        keep = np.diag([1.,np.sqrt(s),np.sqrt(s)])
        loss = [np.sqrt(1-s)*np.outer(np.eye(3)[0],np.eye(3)[i]) for i in (1,2)]
        ops = [keep,*loss]
        assert np.allclose(sum(k.conj().T@k for k in ops),np.eye(3))
        big = [np.kron(np.eye(2),k) for k in ops]
        def channel(mat):
            return sum(k@mat@k.conj().T for k in big)
        reset = channel(rho)
        assert np.max(abs(marginal(reset)-marginal(rho)))<1e-14
        u = np.eye(3,dtype=complex)
        u[1:,1:] = unitary_group.rvs(2,random_state=rng)
        rot = np.kron(np.eye(2),u)
        assert np.allclose(rot@reset@rot.conj().T,channel(rot@rho@rot.conj().T))
    # The selected lab fidelity constrains production of an orthogonal branch, not its lifetime.
    return {"selected_full_emission_tag_cap_at_central_F":2*(1-.941),
            "cap_using_F_minus_two_reported_errors":2*(1-(.941-2*.005)),
            "rate_upper_times_age_100_reads_no_misses_95pct":-np.log(.05)/100}


def aging():
    neutral = json.loads((ROOT/"verification/radiation-reference-results.json").read_bytes())["neutral"]
    ga,gb = neutral["rate_1s_per_s"],neutral["rate_2s_per_s"]
    p = ga/(ga+gb)
    w = 1-p
    x = .5
    curve = np.array([w+(1-w)*x**i for i in range(4)])
    # This pair of strictly positive rates reproduces the first *three* reads.
    mean, variance = curve[1], curve[2]-curve[1]**2
    low = .25
    high = mean+variance/(mean-low)
    weight = (mean-low)/(high-low)
    mimic = np.array([weight*high**i+(1-weight)*low**i for i in range(4)])
    assert 0<low<mean<high<1 and np.allclose(mimic[:3],curve[:3])
    diff = -np.diff(curve)
    D = diff[0]*diff[2]-diff[1]**2
    assert abs(D)<1e-14 and abs(w-(mean-x)/(1-x))<1e-14
    assert abs((np.diff(mimic)[0]*np.diff(mimic)[2]-np.diff(mimic)[1]**2))>1e-4
    # Independently integrate the probability current to both daughters and solve
    # a three-level rate equation in elapsed lifetimes.
    master = np.array([[-1.,0.,0.],[p,0.,0.],[1-p,0.,0.]])
    for n, remain in enumerate(curve):
        age = n*np.log(2.)
        pop = expm(age*master)@np.array([1.,0.,0.])
        assert np.allclose([np.exp(-age),remain],[pop[0],1-pop[1]])
        assert abs(quad(lambda t:p*np.exp(-t),0,age)[0]-(1-remain))<1e-14
    return {"half_life_s":np.log(2)/(ga+gb),"equally_spaced_survival":curve.tolist(),
            "erasure_on_either":[x**i for i in range(4)],"permanent_weight_in_stationary_class":w,
            "alternative_without_permanent":{"low":low,"high":high,"weight_high":weight,"observations":mimic.tolist()},
            "fourth_read_difference":float(curve[3]-mimic[3]),
            "rate_gap_lower_bound_example":(curve[3]-x**3)/(1-x**3)}


def collective_clock():
    rates = json.loads((ROOT/"verification/radiation-reference-results.json").read_bytes())["neutral"]
    ga, gb = rates["rate_1s_per_s"], rates["rate_2s_per_s"]
    w = lambda x: 15*(1-x*x)**2/16
    assert abs(quad(w,-1,1)[0]-1)<1e-14
    assert abs(quad(lambda x:x*x*w(x),-1,1)[0]-1/7)<1e-14
    rows = {}
    for z in (0., .03125, .2, .4, 1., 3.):
        lost = quad(lambda x:w(x)*2*np.sin(z*x/2)**2, -1,1, epsabs=4e-15)[0]
        spectral = 1-15*spherical_jn(2,z)/z**2 if z else 0.
        assert abs(spectral-lost)<5e-15
        dec = gb+ga*lost
        # The common daughter has a 2 x 2 Gram matrix. The distinguishable
        # daughter contributes the identity on the complete one-excitation space.
        gram = ga*np.array([[1,1-lost],[1-lost,1]])+gb*np.eye(2)
        assert abs(np.linalg.eigvalsh(gram)[0]-dec)<1
        rows[str(z)]=float(lost)
    return {"single_line_loss_fraction":rows,
            "width_a_spectator_at_z_a_0p2":gb+ga*rows["0.2"],
            "width_b_spectator_same_spacing":ga+gb*rows["0.03125"],
            "max_half_life_a_spectator_fs":1e15*np.log(2)/gb,
            "max_half_life_b_spectator_fs":1e15*np.log(2)/ga,
            "tenfold_bound_time_fs":1e15*np.log(10)/gb}


def recoil(pair, mass):
    a,b = (np.array(pair[k][1:]) for k in ("early","late"))
    baseline = np.linalg.norm(a+b)
    transverse = np.linalg.norm(a[:2])*np.linalg.norm(b[:2])
    cross = a[:2]@b[:2]
    planar_square = a[:2]@a[:2]+b[:2]@b[:2]
    longitudinal = (a[2]+b[2])**2
    # A common unknown angle preserves every kick magnitude. Independent
    # uniform angles retain the longitudinal impulse and erase one cross term.
    uniform_square = planar_square + longitudinal
    angle = np.arange(1024)*2*np.pi/1024
    dot_rotated = cross*np.cos(angle)+(a[1]*b[0]-a[0]*b[1])*np.sin(angle)
    masses_squared_shift = 2*(cross-dot_rotated)
    assert np.isclose(np.mean(masses_squared_shift),2*cross,atol=4e-20)
    assert np.isclose(np.std(masses_squared_shift),np.sqrt(2)*transverse,atol=4e-20)
    assert abs(np.mean(uniform_square+2*dot_rotated)-uniform_square)<3e-20
    def scale(p):
        return float(p*KMS/mass)
    return {"coherent_kick_kms":scale(baseline),"independent_rms_kms":scale(np.sqrt(uniform_square)),
            "mass_squared_shift_mean":float(2*cross),"mass_squared_shift_sd":float(np.sqrt(2)*transverse),
            "angle_degrees":float(np.rad2deg(np.arccos(np.clip(cross/transverse,-1,1)))) if transverse>1e-22 else None}


def compare_mergers():
    data = json.loads((ROOT/"data/processed/rit-merger-flux.json").read_bytes())
    output = {}
    for name,row in data.items():
        cuts = {c:recoil(v,row["remnant_mass"]) for c,v in row["cut_offsets_M"].items()}
        checks = {c:recoil(v,row["remnant_mass"]) for c,v in row["sensitivity"].items()}
        delta = abs(cuts["0"]["coherent_kick_kms"]-row["metadata_kick_kms"])
        assert delta<6
        output[name] = {"q":row["q"],"catalog_metadata_kick_kms":row["metadata_kick_kms"],
                        "by_peak_offset_M":cuts,"sensitivity":checks}
    return output


def figure(moments,mergers):
    plt.rcParams.update({"font.size":9,"pdf.fonttype":42,"axes.spines.top":False,"axes.spines.right":False})
    t = np.linspace(0,6,250)
    w = moments["permanent_weight_in_stationary_class"]
    alt = moments["alternative_without_permanent"]
    fig, (left,right) = plt.subplots(1,2,figsize=(6.35,2.75),layout="constrained")
    left.plot(t,w+(1-w)*.5**t,color="#1a5879",label="One stable fraction")
    left.plot(t,alt["weight_high"]*alt["high"]**t+(1-alt["weight_high"])*alt["low"]**t,"--",
              color="#a24b28",label="Two finite lifetimes")
    left.scatter(np.arange(4),moments["equally_spaced_survival"],color="#1a5879",s=13)
    left.set(xlabel="Age in half-lives",ylabel="Probability of recalling the mark",ylim=(-.015,1.05))
    left.legend(fontsize=7)
    for tag,label,color in (("RIT:BBH:0119-n140","1:4","#1a5879"),("RIT:BBH:0114-n140","3:4","#a24b28")):
        vals=mergers[tag]["by_peak_offset_M"]
        x=np.array(sorted(map(int,vals)))
        right.plot(x,[vals[str(c)]["independent_rms_kms"] for c in x],"o-",ms=3,color=color,label=label+" separate")
        right.axhline(vals["0"]["coherent_kick_kms"],color=color,ls="--",label=label+" common")
    right.set(xlabel="Split relative to peak power ($M$)",ylabel="Transverse-dominated recoil (km/s)",xticks=[-20,0,20])
    right.legend(fontsize=7,ncol=2,loc="upper center",bbox_to_anchor=(.5,1.02))
    fig.savefig(ROOT/"manuscripts/record_lifetimes.pdf",metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)


if __name__=="__main__":
    moments = aging()
    mergers = compare_mergers()
    results = {"survival":moments,"collective":collective_clock(),"readout":record_channel(),"mergers":mergers}
    (ROOT/"verification/record-lifetime-results.json").write_text(
        json.dumps(results,indent=2,allow_nan=False)+"\n",encoding="utf8")
    figure(moments,mergers)
    print(json.dumps(moments,indent=2))
