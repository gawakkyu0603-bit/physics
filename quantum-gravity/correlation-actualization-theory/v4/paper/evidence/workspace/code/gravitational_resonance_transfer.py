"""Source--packet quantum channel at an isolated gravitational scalar resonance."""
from math import acos, comb, factorial, pi, sqrt

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from scipy.special import eval_genlaguerre


def hydrogenic(n, ell, r):
    scale=(2/n)**1.5*sqrt(factorial(n-ell-1)/(2*n*factorial(n+ell)))
    return scale*np.exp(-r/n)*(2*r/n)**ell*eval_genlaguerre(n-ell-1,2*ell+1,2*r/n)


def transition(upper, lower, angular):
    radial=quad(lambda r:r**4*hydrogenic(*upper,r)*hydrogenic(*lower,r),0,np.inf,epsabs=2e-10)[0]
    omega=(lower[0]**-2-upper[0]**-2)/2
    return dict(radial_integral=radial,frequency_over_binding_unit=omega,
                width_over_G_mu3_alpha6=(2/5)*angular*radial**2*omega**5)


def source_response():
    """Apply the actual two-body cut to half of a normalized Bell pair, tracing the atom."""
    dim=5
    eye=np.eye(dim)
    # The invariant metric on V2 can be absorbed into a change of packet basis.
    bell=eye.flatten()/sqrt(dim)
    proj=np.outer(bell,bell)
    other=np.eye(dim**2)-proj
    initial=np.kron(proj,eye/dim)
    swap=np.eye(dim**2).reshape(dim,dim,dim,dim).transpose(0,1,3,2).reshape(dim**2,dim**2)
    rows=[]
    for q,width in [(.25,0.),(.25,2/5),(1.,0.),(1.,2/5),(.05,.2)]:
        phase=1-2*q+2j*sqrt(q*(1-q))
        unit=other+phase*proj
        selection=q*width
        out=np.zeros_like(initial,dtype=complex)
        for a,kraus in [(1-selection,unit),(selection,phase*proj),(selection,other)]:
            K=np.kron(eye,kraus)
            out+=a*(K@initial@K.conj().T)
        six=out.reshape([dim]*6)
        packet=np.trace(six,axis1=1,axis2=4).reshape(dim**2,dim**2)
        atom=np.trace(six,axis1=2,axis2=5).reshape(dim**2,dim**2)
        t=(4*q+2*width*q*(1-2*q))/dim**2
        assert np.max(abs(packet-((1+t)*np.eye(dim**2)/dim**2-t*swap/dim)))<2e-15
        assert np.max(abs(atom-((1-t)*proj+t*np.eye(dim**2)/dim**2)))<2e-15
        witness=float(np.trace(swap@packet).real)
        neg=float(max(0,-np.linalg.eigvalsh(packet.reshape([dim]*4).transpose(0,3,2,1).reshape(dim**2,dim**2))[0]))
        rows.append([q,width,t,witness,neg])
    atom=[transition((4,0),(3,2),2/3),transition((3,2),(1,0),2/15),transition((3,2),(2,0),2/15)]
    natural_ratio=(atom[1]["width_over_G_mu3_alpha6"]+atom[2]["width_over_G_mu3_alpha6"])/atom[0]["width_over_G_mu3_alpha6"]
    assert abs(natural_ratio-627.1106781)<2e-7
    # J=2 stable spectator in the orbital ground state. A resolved 3d,J=0
    # intermediate state can decay to the elastic 1s or the inelastic 2s line.
    branch=atom[1]["width_over_G_mu3_alpha6"]/(atom[1]["width_over_G_mu3_alpha6"]+atom[2]["width_over_G_mu3_alpha6"])
    y=sqrt(4*branch-1)
    s=1-2*branch/(1-1j*y)
    q=abs(1-s)**2/4
    lost=1-abs(s)**2
    tests=[]
    for thickness in [0.,1/6,2/5]:
        sigma_rows=[]
        coherence=1-thickness*q
        z=coherence*s-1
        gain=1+abs(s)**2-2*coherence*s.real
        for weights in [[.2]*5,[.5,0.,0.,0.,.5]]:
            sigma=np.diag(weights)
            complete=np.zeros((dim*dim,dim*dim),complex)
            for i in range(dim):
                for j in range(dim):
                    E=np.zeros((dim,dim))
                    E[i,j]=1
                    N=np.trace(E)*sigma+(z*E.T@sigma+z.conjugate()*sigma@E.T)/dim+gain*np.trace(E.T@sigma)*eye/dim**2
                    complete+=np.kron(E,N)/dim
            p_el=np.trace(complete).real
            assert abs(p_el-(1-lost/dim**2))<2e-14
            pt=(complete/p_el).reshape([dim]*4).transpose(0,3,2,1).reshape(dim**2,dim**2)
            smallest=np.linalg.eigvalsh(pt)[0]
            if weights[1]==0:
                block=pt[np.ix_([0,6],[0,6])]
                assert abs(np.linalg.det(block)+abs(z)**2*.25/(dim**4*p_el**2))<1e-15 and smallest<0
            else:
                parameter=(1+thickness*branch/4)/(24+branch)
                assert abs(smallest-((1+parameter)/25-parameter))<3e-14
            sigma_rows.append(float(smallest))
        tests.append([thickness,*sigma_rows])
    dipole=quad(lambda r:r**3*hydrogenic(3,2,r)*hydrogenic(2,1,r),0,np.inf)[0]
    vector_width=(16/3)*(2/5)*(5/72)**3*dipole**2
    alpha2_min=vector_width/(3*atom[1]["width_over_G_mu3_alpha6"]-atom[2]["width_over_G_mu3_alpha6"])
    assert alpha2_min>1
    from natural_flux_endpoints import tensor_horizon
    x0=.7
    occupation=tensor_horizon(x0,24.,7)[0]/np.expm1(4*np.pi*x0)
    integral=quad(lambda y:branch**2/(1+y*y)*(1-4*branch*(1-branch)/(25*(1+y*y))),-np.inf,np.inf)[0]
    write_per_width=5*occupation*integral/(4*np.pi)
    assert abs(write_per_width/(1.25*occupation*branch**2*(1-2*branch*(1-branch)/25))-1)<1e-12
    def cone_weights(c):
        def angular(v,k):
            u=(1+v)/2
            return comb(4,k)*(u**k*(1-u)**(4-k)+u**(4-k)*(1-u)**k)/2
        return np.array([quad(angular,c,1,args=(k,))[0]/(1-c) for k in range(5)])
    def cone_test(c):
        p=cone_weights(c)
        z=s-1
        B=abs(z)**2
        factor=5+B/5
        H=sum(1/p)
        diag=(factor*np.diag(p)+z*p[:,None]+z.conjugate()*p[None,:])/25
        det_criterion=factor**2+10*factor*z.real-abs(z)**2*(H-25)
        assert (np.linalg.eigvalsh(diag)[0] < 0)==(det_criterion < 0) or abs(det_criterion)<2e-11
        return H
    critical=brentq(lambda c:cone_test(c)-(26+branch/25),0,.9)
    spinful=dict(critical_cone_cosine=critical,critical_half_angle_degrees=acos(critical)*180/pi,
                 matched_Hawking_occupation=occupation,elastic_write_per_width_and_mismatch=write_per_width,
                 kk_dipole_radial=dipole,kk_vector_width_coefficient=vector_width,
                 kk_matched_minimum_alpha_squared=alpha2_min,branch_to_ground=branch,matched_detuning_over_halfwidth=y,elastic_cut_probability=q,
                 elastic_output_probability=1-lost/dim**2,partial_transpose_minima=tests,
                 geodetic_gap_over_width_prefactor=1/(270*(atom[1]["width_over_G_mu3_alpha6"]+atom[2]["width_over_G_mu3_alpha6"])))
    def redistribution(y):
        q=1/(1+y*y)
        return q*(1-2*q)
    integrated=quad(redistribution,-np.inf,np.inf)[0]
    assert abs(integrated)<1e-13
    return dict(choi_channels=rows,partial_wave_count_flat_integral=integrated,
                gravitational_atom_lines=atom,lower_to_upper_width=natural_ratio,spinful_ground=spinful)
