"""Coarse Lorentzian geometries, energy transferred at an actual contact, and DESI DR2."""
import json
from math import comb, exp, log, sqrt
from pathlib import Path

import numpy as np
from scipy.integrate import quad, solve_ivp
from scipy.linalg import block_diag
from scipy.optimize import brentq, minimize_scalar
from scipy.special import roots_legendre
from scipy.stats import chi2
from scipy.sparse import diags
from scipy.sparse.linalg import expm_multiply

ROOT=Path(__file__).resolve().parents[1]


def dataset():
    z, values, blocks=[], [], []
    for line in (ROOT/"data"/"desi-dr2-bao-table-iv.txt").read_text(encoding="utf8").splitlines():
        if line.startswith("#"): continue
        _, *items=line.split()
        redshift, *row=map(float,items)
        z.append(redshift)
        if len(row)==2:
            val,err=row
            values.append(val)
            blocks.append(np.array([[err**2]]))
        else:
            dm,em,dh,eh,corr=row
            values.extend([dm,dh])
            blocks.append(np.array([[em**2,em*eh*corr],[em*eh*corr,eh**2]]))
    return np.array(z),np.array(values),block_diag(*blocks)


class Distances:
    def __init__(self,z,z_switch,order):
        self.z=z
        self.epoch=1/(1+z_switch)
        parts=np.minimum(z,z_switch)
        x,w=roots_legendre(order)
        # Split every line-of-sight integral at the energy-conserving conversion.
        self.nodes=np.column_stack([parts[:,None]*(1+x)/2,
                                    parts[:,None]+(z-parts)[:,None]*(1+x)/2])
        self.weights=np.column_stack([parts[:,None]*w/2,(z-parts)[:,None]*w/2])

    def inverse_E(self,z,m,f):
        b=1+np.asarray(z)
        vacuum=1-m*(1-f*(1-self.epoch))
        correction=np.minimum(0.,self.epoch*b-1)
        return 1/np.sqrt(vacuum+m*b**3*(1+f*correction))

    def ratios(self,m,f):
        dh=self.inverse_E(self.z,m,f)
        dm=np.sum(self.weights*self.inverse_E(self.nodes,m,f),axis=1)
        pairs=np.column_stack((dm[1:],dh[1:])).ravel()
        return np.r_[(self.z[0]*dh[0]*dm[0]**2)**(1/3),pairs]


def profile(z_switch,order,critical=3.841459):
    z,values,cov=dataset()
    response=Distances(z,z_switch,order)
    inv=np.linalg.inv(cov)
    def score(m,f):
        v=response.ratios(m,f)
        amplitude=(v@inv@values)/(v@inv@v)
        residual=values-amplitude*v
        return float(residual@inv@residual),float(amplitude)
    def fit(f):
        best=minimize_scalar(lambda m:score(m,f)[0],bounds=(.06,.85),method="bounded",
                             options={"xatol":1e-12})
        return float(best.fun),float(best.x),score(best.x,f)[1]
    inner=minimize_scalar(lambda f:fit(f)[0],bounds=(0.,.5),method="bounded")
    best=min((fit(f)[0],f) for f in (0.,float(inner.x),.5))
    chi,f=best
    line=lambda value:fit(value)[0]-chi-critical
    low=brentq(line,0.,f) if f>0 and line(0.)>0 else 0.
    high=brentq(line,f,.5) if f<.5 and line(.5)>0 else .5
    base,m0,a0=fit(0.)
    merr=[brentq(lambda m:score(m,0.)[0]-base-1,.22,m0),
          brentq(lambda m:score(m,0.)[0]-base-1,m0,.38)]
    curve=[[float(ff),*fit(ff)] for ff in np.linspace(0,.5,51)]
    m=fit(f)[1]
    direct=np.array([quad(lambda x:response.inverse_E(x,m,f),0,zz,
                     points=[z_switch] if zz>z_switch else [],epsabs=2e-12)[0] for zz in z])
    vals=np.sum(response.weights*response.inverse_E(response.nodes,m,f),axis=1)
    assert np.max(abs(vals-direct))<2e-12
    return dict(contact_redshift=z_switch,best_fraction=f,best_chi2=chi,best_mass=m,
                best_distance_scale=fit(f)[2],support=[low,high],
                released_fraction_half=fit(.5)[0],baseline=[base,m0,a0,*merr],
                gr_edS_chi2=score(1.,0.)[0],baseline_tail=chi2.sf(base,11),curve=curve)


def geometry():
    rows=[]
    for lapse,scale in ((.7,[1.1,.85,2.]),(1.3,[.5,.5,.5]),(1.1,[.7,1.6,.8])):
        a=np.array(scale)
        v=np.prod(a)
        w=np.r_[v/lapse,lapse*v/a**2]
        dens=sqrt(np.prod(w))
        inv=np.sqrt(dens/w)
        assert np.allclose(inv,np.r_[lapse,a])
        rows.append([*w,*inv])
    histories=[]
    for p in (0,2,4,6):
        n=25000
        scale=sqrt(comb(n+p,p))
        a2=sqrt(comb(2*n+p,p))
        histories.append([p,log(a2/scale)/log(2),p/(p+2)])
    # Consistency in inhomogeneous static vacuum: transport through the horizon is regular in river coordinates.
    mh=.02
    lam=.12
    f=lambda r:1-2*mh/r-lam*r*r/3
    turn=(3*mh/lam)**(1/3)
    black=brentq(f,1e-8,turn)
    cosm=brentq(f,turn,50.)
    assert 9*lam*mh**2<1 and black<turn<cosm
    def characteristic(lo,hi,vac,mass,rad):
        return -4/sqrt(3)*quad(lambda u:sqrt(vac*u*u+mass+rad/u**(2/3)),lo,hi,epsabs=1e-12)[0]
    lo,mid,hi=.42,.83,1.46
    M=.85
    R=.13
    one=characteristic(lo,hi,lam,M,R)
    parts=characteristic(lo,mid,lam,M,R)+characteristic(mid,hi,lam,M,R)
    assert abs(one-parts)<3e-14
    dlam=1e-5
    divided=-(characteristic(lo,hi,lam+dlam,M,R)-characteristic(lo,hi,lam-dlam,M,R))/(2*dlam)
    fourvol=quad(lambda u:2/sqrt(3)*u*u/sqrt(lam*u*u+M+R/u**(2/3)),lo,hi)[0]
    assert abs(divided-fourvol)<1e-9
    proper=quad(lambda u:2/sqrt(3)/sqrt(lam*u*u+M),lo,hi)[0]
    analytic=2/sqrt(3*lam)*(np.arcsinh(hi*sqrt(lam/M))-np.arcsinh(lo*sqrt(lam/M)))
    assert abs(proper-analytic)<5e-15
    return dict(metric_examples=rows,pascal=histories,static_example=[mh,lam,black,turn,cosm],
                link_action=one,link_split_residual=abs(one-parts),volume_from_lambda=fourvol,
                characteristic_derivative_residual=abs(divided-fourvol),dust_vacuum_proper_time=proper)


def pair_volume(observed_matter):
    # Two primitive occupation numbers are constrained to agree. The action couples
    # adjacent occupations with the Bose matrix element n+1 in either direction.
    overlap=1/sqrt(2)
    lam=1.
    K=4*overlap**2-(lam-2)**2
    target=4*overlap**2*(1-observed_matter)/(K*observed_matter)
    now=2/np.sqrt(K)*np.arcsinh(sqrt(K*target/(4*overlap**2)))
    def ordinary(z,sector,t,limit):
        n=np.arange(limit+1.)
        off=z*(n[1:])
        H=diags([off,(sector-2)*(n+.5),off],[-1,0,1],format="csr")
        vacuum=np.zeros(len(n),dtype=complex)
        vacuum[0]=1.
        evolved=expm_multiply((-1j*t)*H,vacuum)
        prob=abs(evolved)**2
        avg=prob@n
        return np.array([avg,prob@((n-avg)**2),sum(prob),prob[-1]])
    cases=[]
    for z,sector,t in [(overlap,1.,now),(1.,0.,1.3),(.6,0.,1.3),(0.,1.,.8)]:
        k=4*z*z-(sector-2)**2
        if abs(k)<1e-12:
            n=z*z*t*t
        elif k>0:
            n=4*z*z/k*np.sinh(sqrt(k)*t/2)**2
        else:
            n=4*z*z/(-k)*np.sin(sqrt(-k)*t/2)**2
        raw=ordinary(z,sector,t,164)
        ref=ordinary(z,sector,t,196)
        assert max(abs(raw-ref))<3e-10
        assert max(abs(raw[:3]-np.array([n,n*(n+1),1.])))<3e-10
        cases.append([z,sector,t,k,n,raw[1],raw[-1]])
    return dict(cases=cases,mean_pairs_today=target,relational_age=now,
                release_per_eligible_contact=(1-overlap)/2,
                max_vacuum_offset_Lya=target/((1+2.33)**3-1),
                max_redshift_with_half_offset=(1+target/.5)**(1/3)-1,
                cells_for_one_percent=int(np.ceil((1+1/target)/(.01**2))),
                positive_clock_wrong_sign_bound_at_10000=4*overlap**2/(10000*(2-lam)**2))


def structure(z_switch,m,f):
    # Subhorizon and after free streaming across the perturbation. A homogeneous
    # fractional release keeps the density contrast and velocity of the surviving dust.
    epoch=1/(1+z_switch)
    vacuum=1-m*(1-f*(1-epoch))
    def segment(start,end,state,matter,radiation,step):
        def rhs(x,y):
            a=exp(x)
            dust=matter/a**3
            light=radiation/a**4
            H2=vacuum+dust+light
            return [y[1],-(2-(3*dust+4*light)/(2*H2))*y[1]+1.5*dust*y[0]/H2]
        return solve_ivp(rhs,(log(start),log(end)),state,rtol=2e-12,atol=4e-15,
                         dense_output=True,max_step=step,method="DOP853")
    def slopes(step):
        s0=.005
        early=segment(s0,epoch,[s0,s0],m,0.,step)
        late=segment(epoch,1.,early.y[:,-1],(1-f)*m,f*m*epoch,step)
        return np.array([(early if a<epoch else late).sol(log(a))[1]
                         for a in (1/1.067,1/2.36)])
    v=slopes(.08)
    assert np.max(abs(v-slopes(.05)))<4e-11
    ratio=v[1]/v[0]
    # Independent two-point comparison with unknown growth normalization.
    obs=np.array([.423,.482])
    err=np.array([.055,.116])
    amplitude=np.sum(obs*v/err**2)/np.sum((v/err)**2)
    raw=float(np.sum(((amplitude*v-obs)/err)**2))
    return [float(ratio),raw,float(amplitude),*list(amplitude*v)]



def correlated_pair_state():
    # Every site uses the same pair generator. Two allowed phases set the
    # initial sign of the local expansion. Conditional on the signs, the
    # state factors, so the two-site distribution can be evaluated directly.
    z = 1 / sqrt(2)
    detuning = -1.
    k = 4*z**2 - detuning**2
    initial_pairs = .02
    x = -detuning * initial_pairs / (2*z)
    y = sqrt(initial_pairs*(1+initial_pairs)-x*x)
    deficit = 4*z**2*initial_pairs + k*initial_pairs**2
    t = 1.15
    response = np.sinh(sqrt(k)*t)/sqrt(k)
    mean = (initial_pairs+2*z**2/k)*np.cosh(sqrt(k)*t)-2*z**2/k
    signs = np.array([-1, 1])
    occupations = np.arange(97, dtype=float)
    off = z*occupations[1:]
    generator = diags([off,detuning*(occupations+.5),off],[-1,0,1],format="csr")
    marginal = []
    for sign in signs:
        ratio = (x-1j*sign*y)/(1+initial_pairs)
        initial = ratio**occupations / sqrt(1+initial_pairs)
        prob = abs(expm_multiply((-1j*t)*generator,initial))**2
        assert abs(prob.sum()-1)<1e-12
        assert abs(prob@occupations-mean-sign*sqrt(deficit)*response)<1e-11
        marginal.append(prob)
    covariances = []
    for contact_correlation in (-.4,0.,.4,1.):
        joint = np.zeros((len(occupations),len(occupations)))
        for i, left in enumerate(signs):
            for j, right in enumerate(signs):
                weight = (1+contact_correlation*left*right)/4
                joint += weight * np.outer(marginal[i],marginal[j])
        covariance = float(occupations@joint@occupations - mean**2)
        assert abs(covariance-contact_correlation*deficit*response**2)<2e-11
        covariances.append([contact_correlation,covariance])
    return dict(initial_mean=initial_pairs,initial_x=x,initial_y_magnitude=y,
                negative_stiff_numerator=deficit,clock_time=t,mean=mean,
                two_site_covariances=covariances)


def stiff_profile(order, existence_redshift=None):
    # Fit only the redshift interval actually covered by the published distances.
    # Positivity of E^2 on the whole interval follows from its concavity in (1+z)^3.
    redshifts, values, covariance = dataset()
    precision = np.linalg.inv(covariance)
    nodes, weights = roots_legendre(order)
    evaluation = redshifts[:,None]*(1+nodes)/2
    quadrature = redshifts[:,None]*weights/2
    last_source = redshifts[-1] if existence_redshift is None else max(redshifts[-1],existence_redshift)
    highest = (1+last_source)**3
    def inverse_rate(redshift, mass, stiff):
        u = (1+redshift)**3
        return 1/np.sqrt(1+mass*(u-1)-stiff*(u*u-1))
    def score(mass, stiff):
        dm = np.sum(quadrature*inverse_rate(evaluation,mass,stiff),axis=1)
        dh = inverse_rate(redshifts,mass,stiff)
        v = np.r_[(redshifts[0]*dh[0]*dm[0]**2)**(1/3),
                  np.column_stack((dm[1:],dh[1:])).ravel()]
        scale = (v@precision@values)/(v@precision@v)
        residual = values-scale*v
        return float(residual@precision@residual),float(scale)
    def fit(stiff):
        minimum_mass = max(0.,stiff*(highest+1)-1/(highest-1))
        upper_mass = 1+stiff
        opt = minimize_scalar(lambda mass:score(mass,stiff)[0],
                              bounds=(minimum_mass,upper_mass),method="bounded",
                              options={"xatol":1e-13})
        assert opt.success
        return (float(opt.fun),float(opt.x),score(opt.x,stiff)[1])
    # Beyond this s a positive vacuum term is incompatible with reaching the last bin.
    maximum = 1/(highest-1)
    grid = np.linspace(0,maximum*(1-1e-5),181)
    scores = np.array([fit(s)[0] for s in grid])
    index = int(np.argmin(scores))
    left = grid[max(0,index-1)]
    right = grid[min(index+1,len(grid)-1)]
    candidate = minimize_scalar(lambda s:fit(s)[0],bounds=(left,right),method="bounded",
                                options={"xatol":1e-14}).x
    best_chi, best_stiff = min((fit(s)[0],float(s)) for s in (left,candidate,right))
    upper = brentq(lambda s:fit(s)[0]-best_chi-3.841459,best_stiff,grid[-1],xtol=1e-14)
    assert np.all(scores[grid>upper]>best_chi+3.841459)
    m_upper = fit(upper)[1]
    vals = np.sum(quadrature*inverse_rate(evaluation,m_upper,upper),axis=1)
    direct = [quad(inverse_rate,0.,zz,args=(m_upper,upper),epsabs=2e-12)[0] for zz in redshifts]
    assert np.max(abs(vals-direct))<2e-11
    # On the demonstrative K=1, 4 z^2=2 family with symmetric signs h=A0/2.
    # Translate the fitted (m,s) without fixing an independently fitted epoch.
    def microscopic(m,s):
        vacuum = 1-m+s
        present_pairs = 2*vacuum/m
        deficit = s*present_pairs**2/vacuum
        q = deficit/(1+sqrt(1+deficit))
        return dict(present_pairs=present_pairs,minimum_pairs=q,
                    numerator=deficit,bounce_redshift=(present_pairs/q)**(1/3)-1 if q else None)
    return dict(best_stiff=best_stiff,best_chi2=best_chi,best_mass=fit(best_stiff)[1],
                baseline_chi2=fit(0.)[0],profile_upper=upper,upper_mass=m_upper,
                upper_distance_scale=fit(upper)[2],upper_state=microscopic(m_upper,upper),
                best_state=microscopic(fit(best_stiff)[1],best_stiff),max_positive_domain=maximum)


def main():
    profiles=[profile(z,26) for z in (.5,1.,2.)]
    fine=[profile(z,40) for z in (.5,1.,2.)]
    for a,b in zip(profiles,fine):
        assert abs(a["best_chi2"]-b["best_chi2"])<2e-9
        assert abs(a["support"][1]-b["support"][1])<1e-8
    baseline=profiles[0]["baseline"]
    assert abs(baseline[1]-.2975)<.001 and abs(2997.92458/baseline[2]-101.54)<.1
    z=.934
    floor=2*(1+z)*(sqrt(1+z)-1)
    # Published AP observable is used only for this separate one-bin inequality.
    growth=[]
    for entry in profiles:
        for f in (0.,.10,.5):
            m=entry['curve'][round(f*100)][2]
            growth.append([entry['contact_redshift'],f,m,*structure(entry['contact_redshift'],m,f)])
    stiff = stiff_profile(32)
    refined_stiff = stiff_profile(58)
    for key in ("best_chi2","profile_upper","upper_mass"):
        assert abs(stiff[key]-refined_stiff[key])<5e-8
    # The oxygen line supplies only a redshift-existence condition, with no distance likelihood.
    galaxy = stiff_profile(32,14.1793)
    assert 0 < galaxy["profile_upper"] < stiff["profile_upper"]
    correlated = correlated_pair_state()
    inband=2.8e-9*log(1726/20)
    # The published bound uses a uniform energy density per log frequency across its analysis band.
    source_mass=profiles[1]['curve'][10][2]
    result=dict(geometry=geometry(),profiles=profiles,structure_growth=growth,
                primitive_volume=pair_volume(baseline[1]),
                correlated_pair_state=correlated,stiff_fit=stiff,stiff_with_galaxy=galaxy,
                flat_tensor_band=dict(band_Hz=[20,1726],max_integral=inband,
                                      max_release_times_band_fraction_z1=inband/(source_mass/2),
                                      max_band_fraction_at_release_point1=inband/(.1*source_mass/2)),
                dust_radiation_AP=dict(z=z,minimum=floor,measurement=1.223,sigma=.019,
                                       discrepancy=(floor-1.223)/.019))
    (ROOT/"verification"/"landscape-receipts-results.json").write_text(
        json.dumps(result,indent=2,allow_nan=False)+"\n",encoding="utf8")
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig,axes=plt.subplots(1,2,figsize=(8.1,3.1),layout="constrained")
    for p,col in ((0,"#414d61"),(2,"#157574"),(4,"#a34f32")):
        ns=range(1,36)
        a=np.array([sqrt(comb(n+p,p)) for n in ns])
        axes[0].plot(list(ns),a/a[9],color=col,label={0:"Static",2:"Radiation scaling",4:"Dust scaling"}[p])
    axes[0].set(xlabel="Ordered contact slice",ylabel="Relative scale factor")
    axes[0].legend(frameon=False,fontsize=7)
    for entry,col in zip(profiles,("#875788","#157574","#a34f32")):
        f,chis=np.array(entry["curve"])[:,:2].T
        axes[1].plot(f,chis-entry["best_chi2"],color=col,label=fr"$z_*={entry['contact_redshift']:g}$")
    axes[1].axhline(3.841459,color="#666",lw=.8,ls=":")
    axes[1].set(xlabel="Fraction of initial dust energy released",ylabel=r"Profile $\Delta\chi^2$",ylim=(-.15,14))
    axes[1].legend(frameon=False,fontsize=7)
    for ax in axes:ax.spines[["top","right"]].set_visible(False)
    fig.savefig(ROOT/"manuscripts"/"landscape_receipts.pdf",metadata={"CreationDate":None,"ModDate":None})
    plt.close(fig)
    for p in profiles:
        print(p["contact_redshift"],p["best_fraction"],p["best_chi2"],p["support"])
    print("Flat background",baseline, "no-acceleration floor",floor)


if __name__=="__main__":
    main()
