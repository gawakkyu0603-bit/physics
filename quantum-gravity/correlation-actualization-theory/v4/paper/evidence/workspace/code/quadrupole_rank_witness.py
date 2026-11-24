"""Exact finite-field witness for the plane-wave center's four-quadrupole response."""
from itertools import product

import numpy as np
from scipy.sparse import csr_matrix

PRIME = 101


def invariant_coefficients():
    # An STF Cartesian tensor is expanded in its xx, yy, xy, xz, yz components.
    basis = []
    for i,j in [(0,0),(1,1),(0,1),(0,2),(1,2)]:
        a = np.zeros((3,3),dtype=np.int64)
        a[i,j]=a[j,i]=1
        if i==j:
            a[2,2]=-1
        basis.append(a)
    tensors=[]
    for a,b,c,d in product(basis,repeat=4):
        tensors.append([np.trace(a@b)*np.trace(c@d),np.trace(a@c)*np.trace(b@d),
                        np.trace(a@d)*np.trace(b@c),np.trace(a@b@c@d),np.trace(a@c@b@d)])
    return np.array(tensors)


def amplitudes(initial, coefficients, phases):
    cutoff = sum(initial)+8
    states = [s for s in product(range(cutoff+1),repeat=3) if sum(s)<=cutoff]
    where = dict(zip(states,range(len(states))))
    plus,minus=[],[]
    for axis in range(3):
        up=np.zeros((len(states),len(states)),dtype=np.int64)
        down=np.zeros_like(up)
        for i,s in enumerate(states):
            if sum(s)<cutoff:
                nxt=list(s)
                nxt[axis]+=1
                up[where[tuple(nxt)],i]=1
            if s[axis]:
                nxt=list(s)
                nxt[axis]-=1
                down[where[tuple(nxt)],i]=s[axis]
        plus.append(csr_matrix(up))
        minus.append(csr_matrix(down))
    out = np.zeros((len(states),1),dtype=np.int64)
    out[where[initial],0]=1
    for phase in phases:
        coords=[phase*u+pow(phase,-1,PRIME)*d for u,d in zip(plus,minus)]
        x,y,z=coords
        squares = [v@v for v in coords]
        # Q' = 3*Q; the omitted common normalization cannot affect rank.
        trace = sum(squares[1:],squares[0])
        quad=[3*squares[0]-trace,3*squares[1]-trace,3*(x@y),3*(x@z),3*(y@z)]
        out=np.stack([(q@out)%PRIME for q in quad],axis=-1).reshape(len(states),-1)
    return states,(out@coefficients)%PRIME


def determinant(rows):
    a = np.array(rows,dtype=np.int64).copy()
    det=1
    for k in range(len(a)):
        pivot=next((j for j in range(k,len(a)) if a[j,k]%PRIME),None)
        if pivot is None:
            return 0
        if pivot!=k:
            a[[pivot,k]]=a[[k,pivot]]
            det=-det
        v=int(a[k,k])%PRIME
        det=det*v%PRIME
        for j in range(k+1,len(a)):
            a[j]=(a[j]-a[j,k]*pow(v,-1,PRIME)*a[k])%PRIME
    return det%PRIME


def witness():
    # exp(it) = 1, (3+4i)/5, i, (-3+4i)/5. Map i -> 10 in F_101.
    phases=[1,43*pow(5,-1,101)%101,10,37*pow(5,-1,101)%101]
    coeff=invariant_coefficients()
    selected=[]
    reduced=[]
    rows=[]
    pivots=[]
    for initial in [(0,0,0),(1,0,0),(2,0,0),(1,1,0)]:
        final_states,outputs=amplitudes(initial,coeff,phases)
        for final,raw in zip(final_states,outputs):
            v=raw.copy()
            for pivot,old in zip(pivots,reduced):
                v=(v-v[pivot]*old)%PRIME
            if np.any(v):
                pivot=int(np.flatnonzero(v)[0])
                reduced.append((v*pow(int(v[pivot]),-1,PRIME))%PRIME)
                pivots.append(pivot)
                selected.append([list(initial),list(final)])
                rows.append(raw.tolist())
            if len(rows)==5:
                value=determinant(rows)
                assert value!=0
                return dict(prime=PRIME,phase_residues=phases,fock_pairs=selected,minor=rows,determinant_mod_prime=value)
    raise AssertionError("No full-rank invariant quadrupole minor")


if __name__=="__main__":
    print(witness())
