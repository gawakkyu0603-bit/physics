"""Two graviton blocks on the M circle, with a material reference for a layer."""
from fractions import Fraction
from math import cos, pi, sin

import json
from pathlib import Path

import numpy as np
from scipy.integrate import quad
from scipy.special import ive, kv

ROOT = Path(__file__).resolve().parents[1]


def images(b, y, radius, power, count=40):
    displacements = np.asarray(y)[..., None] + 2*pi*radius*np.arange(-count, count+1)
    return np.sum((b*b + displacements**2)**(-power), axis=-1)


def phase_modes(b, radius, strength):
    # strength = N1*N2*|v|^3 in scalar eigenvalue units. The zero mode is the angle average.
    ratio = b/radius
    modes = np.arange(1, max(2, int(np.ceil(58/ratio))+1))
    z = modes*ratio
    mean = 3*strength/(16*radius*b**5)
    return mean, modes, mean*np.exp(-z)*(1+z+z*z/3)


def periodic_phase(b, y, radius, strength):
    mean, modes, harmonics = phase_modes(b, radius, strength)
    return mean+2*np.sum(harmonics*np.cos(np.asarray(y)[..., None]*modes/radius), axis=-1)


def phase_difference(b, y, separation, radius, strength):
    # The sine series avoids subtracting nearly equal phases for a distant receiver.
    _, modes, harmonics = phase_modes(b, radius, strength)
    return 4*np.sum(harmonics*np.sin(modes*y/radius)*np.sin(modes*separation/(2*radius)))


def compact_checks():
    rows = []
    for radius in (.24, .73, 2.2):
        b, y, v, ranks = 1.15, .39, .23, 6
        q = ranks*v**3
        direct = q*images(b, y, radius, 3, count=140)
        series = periodic_phase(b, y, radius, q)
        timed = 2*quad(lambda t: 15*ranks*v**4/16*images(
            np.hypot(b,v*t),y,radius,3.5,count=140), 0, np.inf,
            epsabs=2e-14, epsrel=3e-12)[0]
        z = b/radius
        static_ratio = z**3*kv(3,z)/8
        coeff = [quad(lambda theta: images(b,radius*theta,radius,3.5,count=85)
                      *cos(m*theta), 0, pi,epsabs=2e-12)[0] for m in (0,1)]
        assert np.allclose([timed,direct],[series,series],rtol=2e-10,atol=3e-14)
        assert abs(coeff[1]/coeff[0]-static_ratio)<3e-11
        rows.append(dict(radius=radius,image_phase=float(direct),fourier_phase=float(series),
                         time_integral=timed,first_static_ratio=static_ratio))
    return rows


def transfer(b, radius, q):
    mean, modes, harmonics = phase_modes(b,radius,q)
    angles = 2*pi*np.arange(2048)/2048
    centered = periodic_phase(b,radius*angles,radius,q)-mean
    amplitudes = np.fft.fft(np.exp(1j*centered))/len(angles)
    power = abs(amplitudes)**2
    probability = float(power[1:].sum())
    variance = float(2*np.dot(harmonics,harmonics))
    # Check the zero-transfer integral separately. Use half-angle at small probabilities.
    real_loss = quad(lambda t: 2*sin((periodic_phase(b,radius*t,radius,q)-mean)/2)**2,
                     0,pi,epsabs=1e-15)[0]/pi
    imag_part = quad(lambda t: sin(periodic_phase(b,radius*t,radius,q)-mean),
                     0,pi,epsabs=1e-14)[0]/pi
    assert abs(probability-(2*real_loss-real_loss**2-imag_part**2))<6e-14
    assert abs(power.sum()-1)<3e-14 and np.max(abs(power[1:]-power[:0:-1]))<3e-14
    mode_number = np.fft.fftfreq(len(angles),d=1/len(angles))
    # Benchmark incoming longitudinal momentum mu*|v|=400/b. Closed tails must be negligible.
    incoming_momentum = 400/b
    closed_weight = float(power[abs(mode_number)>incoming_momentum*radius].sum())
    assert closed_weight<2e-25 and probability<=min(1.,2*mean)+2e-14
    # Taylor's bound applies to the fourth moment of the difference of two independent phases.
    fourth = 2*np.mean(centered**4)+6*np.mean(centered**2)**2
    assert abs(probability-variance)<=fourth/24+2e-14
    return dict(radius=radius,probability=probability,variance=variance,first_harmonic=float(harmonics[0]),
                incoming_relative_momentum=incoming_momentum,closed_eikonal_tail=closed_weight,
                angularly_uniform_echo_loss=2*probability*(1-probability))


def strong_limit():
    # For a state uniform on a growing circle, the probability is diluted by its length.
    # Using the loss instead of subtracting two almost equal overlaps preserves small signals.
    b, strength, y, d = 1., .8, .4, .7
    phase = lambda x: strength/(b*b+x*x)**3
    coefficient = 2/pi*quad(lambda x: 2*sin(phase(x)/2)**2,0,np.inf,epsabs=2e-14)[0]
    local_difference = phase(y-d/2)-phase(y+d/2)
    local_p = sin(local_difference/2)**2
    rows=[]
    for radius in (2.,4.,8.,16.,32.):
        def losses(x):
            delta=strength*images(b,x,radius,3,count=22)
            return 2*sin(delta/2)**2, sin(delta)
        width=pi*radius
        real_loss, imaginary = [quad(lambda x: losses(x)[j],0,width,epsabs=1e-13)[0]/width
                                 for j in range(2)]
        uniform=2*real_loss-real_loss**2-imaginary**2
        difference = strength*(images(b,y-d/2,radius,3)-images(b,y+d/2,radius,3))
        rows.append(dict(radius=radius,uniform=uniform,scaled_uniform=radius*uniform,
                         local_dark=sin(difference/2)**2))
    assert abs(rows[-1]["scaled_uniform"]/coefficient-1)<.009
    assert abs(rows[-1]["local_dark"]-local_p)<1e-13 and local_p>.01
    return dict(uniform_asymptotic_coefficient=coefficient,local_limit=local_p,values=rows)


def readouts():
    # A prepared relative geometry sets the three length scales. The same law is used everywhere.
    strength, radius, y, d = .8, .82, .4, .7
    rows = []
    hadamard = np.array([[1,1],[1,-1]],complex)/np.sqrt(2)
    for impact in (1.,1.6,2.4,4.,8.):
        phases = [periodic_phase(impact,y-shift,radius,strength) for shift in (d/2,-d/2)]
        delta = phase_difference(impact,y,d,radius,strength)
        assert abs(delta-(phases[0]-phases[1]))<2e-14
        unitary = hadamard@np.diag(np.exp(1j*np.array(phases)))@hadamard
        outgoing = unitary[:,0]
        p=sin(delta/2)**2
        assert abs(abs(outgoing[1])**2-p)<3e-15
        reversed_mixture=unitary.conj().T@np.diag(abs(outgoing)**2)@unitary
        wrong=2*p*(1-p)
        assert abs(reversed_mixture[1,1]-wrong)<2e-15
        inner=np.vdot(np.exp(1j*np.array(phases))/np.sqrt(2),
                      np.exp(1j*np.array(phases[::-1]))/np.sqrt(2))
        assert abs(inner-cos(delta))<2e-15
        # Later material trajectories have different impact parameters; the new probe receives momentum.
        kick=lambda r: -6*.19*r*images(r,.22,.82,4)
        momenta=np.array([kick(1.05),kick(1.65)])
        delta_p=float(wrong*(momenta[1]-momenta[0]))
        assert abs(np.dot(np.diag(reversed_mixture).real,momenta)-momenta[0]-delta_p)<2e-15
        rows.append(dict(impact=impact,phase_difference=float(delta),dark=p,wrong_after_undo=wrong,
                         sign_success_quadrature=(1+abs(sin(delta)))/2,
                         extra_late_impulse=delta_p))
    return rows


def hard_gravity_pair():
    # E is one incident graviton energy. Fix an outgoing hemisphere and helicity in a
    # four-dimensional kinematic plane. The angular density uses all nine base spatial momenta.
    rows=[]
    for size in (.8,1.,1.02,1.25,2.,4.,12.,64.,256.):
        charges=np.arange(-int(size),int(size)+1)
        beta=np.sqrt(np.maximum(0.,1-(charges/size)**2))
        for cosine in (0.,.61):
            born_weights=beta**7*(1-cosine**2)**2/(1-(beta*cosine)**2)**2
            # Independent Lorentz-product computation retaining all eleven spacetime components.
            # The first four components below span time, beam, ordinary transverse, compact.
            p1=np.array([1.,1.,0.,0.])
            p2=np.array([1.,-1.,0.,0.])
            invariant=lambda p: p[0]**2-np.dot(p[1:],p[1:])
            reference=[]
            for n,k in zip(charges,beta):
                out=np.array([1.,k*cosine,k*np.sqrt(1-cosine**2),n/size])
                t,u=invariant(p1-out),invariant(p2-out)
                assert abs(invariant(out))<8e-16 and abs(4+t+u)<2e-15
                reference.append(k**7*(4**3/(t*u))**2)
            reference=np.array(reference)
            reference/=reference[charges==0][0]
            assert np.allclose(born_weights,reference,rtol=1e-13,atol=2e-14)
            weights=born_weights/born_weights.sum()
            p0=float(weights[charges==0][0])
            coarse=p0**2+(1-p0)**2
            signed=p0**2+(1-p0)**2/2
            resolved=float(np.dot(weights,weights))
            assert resolved<=signed+4e-15 and signed<=coarse+4e-15 and resolved<=p0+5e-15
            rows.append(dict(energy_times_radius=size,cosine=cosine,zero=p0,formed=1-p0,
                             return_binary=coarse,return_sign=signed,return_integer=resolved))
    coeff=quad(lambda x:(1-x*x)**3.5,-1,1,epsabs=2e-13,epsrel=1e-13)[0]
    assert abs(coeff-35*pi/128)<3e-12
    last=next(row for row in rows if row["energy_times_radius"]==256. and row["cosine"]==0)
    assert abs(256*last["zero"]-1/coeff)<3e-10
    return dict(right_angle_counting_coefficient=coeff,values=rows)


def absorbed_sign():
    # Equal-energy right-angle hard pairs. Each sign emits a different orthogonal partner.
    # The probability of arrival and absorption is supplied by the material response.
    a=12.
    charges=np.arange(-3,4)
    weights=(1-(charges/a)**2)**3.5
    weights/=weights.sum()
    pair=np.diag(np.sqrt(weights)).reshape(-1)
    joint=np.outer(pair,pair)
    local_marginals=[]
    for labels in (charges!=0,np.sign(charges),charges):
        record=np.repeat(labels,len(charges))
        after=joint*(record[:,None]==record[None,:])
        marginal=np.trace(after.reshape([len(charges)]*4),axis1=1,axis2=3)
        local_marginals.append(marginal)
        assert np.allclose(marginal,np.diag(weights),atol=2e-15)
    # The paired order of detector sites is physical. Output states s=+/- are orthogonal.
    eta,phi,phase=.3,pi/2,.82
    for sign in (-1,1):
        arms=np.array([1,np.exp(1j*sign*phase)])/np.sqrt(2)
        basis=np.array([[1,np.exp(-1j*phi)],[1,-np.exp(-1j*phi)]])/np.sqrt(2)
        p=eta*abs(basis@arms)**2
        exact=eta*(1+np.array([1,-1])*cos(phi-sign*phase))/2
        assert np.allclose(p,exact,atol=5e-16)
    denominator=35*pi/256
    rows=[]
    for scaled_baseline in (0.,.1,.5,1.,3.,6.,12.):
        v=quad(lambda x:(1-x*x)**3.5*sin(scaled_baseline*x),0,1,
               epsrel=1e-13,epsabs=1e-14)[0]/denominator
        # At finite radius the zero mode is excluded on conditioning on a signed transfer.
        size=1024.
        n=np.arange(1,int(size))
        w=(1-(n/size)**2)**3.5
        approx=float(w@np.sin(scaled_baseline*n/size)/w.sum())
        assert abs(v-approx)<.0012
        rows.append(dict(energy_times_site_separation=scaled_baseline,
                         continuum_signed_contrast=v,finite_1024_contrast=approx))
    slope=quad(lambda x:x*(1-x*x)**3.5,0,1,epsabs=1e-14,epsrel=1e-13)[0]/denominator
    assert abs(slope-256/(315*pi))<1e-13
    return dict(continuum_small_baseline_slope=slope,contrasts=rows,
                single_received_marginal_error=max(float(np.max(abs(m-local_marginals[0]))) for m in local_marginals))


def material_precision():
    theta=2*pi*np.arange(2048)/2048
    modes=np.fft.fftfreq(len(theta),d=1/len(theta))
    rows=[]
    for localization in (0.,.2,1.,5.,25.):
        state=np.exp(localization*(np.cos(theta)-1))
        state/=np.sqrt(np.mean(state**2))
        gamma=float(np.mean(state**2*np.cos(theta)))
        amplitudes=np.fft.fft(state)/len(theta)
        variance=float(np.sum(modes**2*abs(amplitudes)**2))
        analytic=ive(1,2*localization)/ive(0,2*localization)
        assert abs(gamma-analytic)<2e-15 and abs(variance-localization*analytic/2)<3e-13
        assert gamma**2<=4*variance/(1+4*variance)+3e-14
        # Optimal discrimination of the two actual rotor states with and without one KK kick.
        states=np.column_stack((state,state*np.exp(1j*theta)))/np.sqrt(len(theta))
        _, factors=np.linalg.qr(states,mode="reduced")
        contrast=factors@np.diag([1.,-1.])@factors.conj().T
        distinguishability=float(np.sum(abs(np.linalg.eigvalsh(contrast)))/2)
        assert abs(distinguishability**2+gamma**2-1)<5e-14
        rows.append(dict(localization=localization,first_moment=gamma,charge_variance=variance,
                         upper_squared_moment=4*variance/(1+4*variance),
                         single_transfer_correct=(1+distinguishability)/2))
    return rows


def source_and_selection():
    # Two bosons with either one occupation on each side or both on a single random side.
    # Their mean layer densities coincide, whereas their joint occupations differ.
    alternatives=[(Fraction(1,2),2,0),(Fraction(1,2),0,2)]
    mean_left=sum(w*n for w,n,_ in alternatives)
    mean_right=sum(w*n for w,_,n in alternatives)
    mixed_joint=sum(w*n*m for w,n,m in alternatives)
    assert mean_left==mean_right==1 and mixed_joint==0
    # Exchangeable stations with different responses solely from their material environments.
    p_close,p_far=Fraction(3,4),Fraction(1,4)
    # Conditioning on retaining two concordant records; the selector is stated explicitly.
    prior=Fraction(1,2)
    posterior=prior*p_close**2/(prior*p_close**2+(1-prior)*p_far**2)
    assert posterior==Fraction(9,10)
    return dict(common_mean_per_layer=1,opposite_pair_joint=1,exclusive_joint=int(mixed_joint),
                equal_prior_near_given_two_retained=float(posterior))


def plot(rows, readouts):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig, (left, right) = plt.subplots(1, 2, figsize=(7.3, 2.8), constrained_layout=True)
    radii = [entry["radius"] for entry in rows["values"]]
    left.loglog(radii, [entry["uniform"] for entry in rows["values"]], "o-",
                color="#12636b", label="Uniform input: momentum transfer")
    left.loglog(radii, [entry["local_dark"] for entry in rows["values"]], "s-",
                color="#93471e", label="Local material: dark output")
    left.set(xlabel="Circle radius / impact parameter", ylabel="Probability per encounter")
    left.legend(frameon=False, fontsize=7, loc="lower left")
    impacts = [entry["impact"] for entry in readouts]
    right.semilogy(impacts, [entry["dark"] for entry in readouts], "s-",
                   color="#93471e", label="Irreversible port probability")
    right.semilogy(impacts, [entry["wrong_after_undo"] for entry in readouts], "o--",
                   color="#303f77", label="Changed port after coherent undo")
    right.set(xlabel="Impact parameter (matrix units)", ylabel="Probability per encounter")
    right.legend(frameon=False, fontsize=7)
    dest = ROOT/"manuscripts"
    dest.mkdir(exist_ok=True)
    fig.savefig(dest/"matrix_circle_layers.pdf", metadata={"CreationDate":None, "ModDate":None})
    plt.close(fig)


def main():
    data=dict(kernel=compact_checks(),transfer=[transfer(1.,radius,.31) for radius in
              (.16,.27,.55,1.,2.3)],decompactification=strong_limit(),
              material_readouts=readouts(),material_precision=material_precision(),hard_scattering=hard_gravity_pair(),absorbed_sign=absorbed_sign(),
              joint_stress=source_and_selection())
    out=ROOT/"verification"
    out.mkdir(exist_ok=True)
    (out/"matrix-circle-layer-results.json").write_text(
        json.dumps(data,indent=2,allow_nan=False)+"\n",encoding="utf8")
    plot(data["decompactification"],data["material_readouts"])
    print("Checked image sums, scattering phases, transfer probabilities, material readings and late impulses.")


if __name__=="__main__":
    main()
