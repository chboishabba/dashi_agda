"""Tensor-product fixture: literal outer phase transport, not original MMV.
Use ordinary Lindsey 12/78 source C and the actual TOE kernel compiler.
"""
import json
from pathlib import Path
from itertools import product
import numpy as np
from toe_cyclotomic_operator import compile_shape, columns
from monster3b_lindsey_actual_mod31_join import source_matrices, dual
from monster3b_actual_projective_sym2_intertwiner import inverse

P=31

def require(ok,msg):
    if not ok:raise ValueError(msg)

def eye(n):return np.eye(n,dtype=np.int64)
def mm(a,b):return a@b%P

def inv3(A):
    A=np.concatenate((A.copy()%3,eye(len(A))),axis=1);n=len(A)
    for i in range(n):
        j=next(j for j in range(i,n) if A[j,i]);A[[i,j]]=A[[j,i]]
        A[i]=A[i]*pow(int(A[i,i]),-1,3)%3
        for j in range(n):
            if j!=i:A[j]=(A[j]-A[j,i]*A[i])%3
    return A[:,n:]

def det(A):
    A=A.copy()%P;out=1
    for i in range(len(A)):
        j=next(j for j in range(i,len(A)) if A[j,i])
        if j!=i:A[[i,j]]=A[[j,i]];out=-out
        a=int(A[i,i]);out=out*a%P
        A[i+1:]=(A[i+1:]-A[i+1:,i,None]*pow(a,-1,P)*A[i])%P
    return out%P

def kernel(C,s):
    R=compile_shape(C,2,s);R['scalar']=[1,0,1]
    require(R['origin']==[0,0],'zero origin')
    H=np.zeros((9,9),dtype=np.int64)
    for j,y,(a,b) in columns(R):H[y,j]=np.asarray((a+5*b)%P,dtype=np.int64)*pow(11,-R['rank'],P)%P
    neg=np.array([int(''.join(map(str,(-np.array(x)%3).tolist())),3) for x in product(range(3),repeat=2)])
    reps=np.flatnonzero(np.arange(9)<neg);pos=np.r_[0,reps]
    even=H[np.ix_(pos,pos)].copy();even[:,1:]=(even[:,1:]+H[np.ix_(pos,neg[reps])])%P
    odd=(H[np.ix_(reps,reps)]-H[np.ix_(reps,neg[reps])])%P
    H=H*det(odd)*pow(det(even),-1,P)%P
    require(H[0,0]!=0,'canonical vacuum')
    return H,eye(9)[:,neg],R['rank']

def echelon_columns(A):
    n=A.shape[0];basis=[];piv=[]
    for v in A.T:
        w=v.copy()
        for j,b in zip(piv,basis):w=(w-w[j]*b)%P
        nz=np.flatnonzero(w)
        if not len(nz):raise ValueError('transport lost rank')
        j=int(nz[0]);piv.append(j);basis.append(w*pow(int(w[j]),-1,P)%P)
    require(len(basis)==n,'full rank')
    return np.column_stack(basis)

def run():
    path=Path(__file__).resolve().parents[1]/'Docs/support/reference/Monster3BLindseyOrdinaryCD20261124.json'
    data=json.loads(path.read_text()); T=source_matrices(data,0); U=dual(T['C'],True)
    # Actual ordinary signed 90D outer blocks; 12 and 78 in each phase.
    L=[]
    for i,j in ((1,0),(0,1)):
        A=T['C'][i*12:(i+1)*12,j*12:(j+1)*12]
        B=U[i*78:(i+1)*78,j*78:(j+1)*78]
        L.append(np.block([[A,np.zeros((12,78),dtype=np.int64)],[np.zeros((78,12),dtype=np.int64),B]]))
    J90=np.diag([-1]*12+[1]*78)%P
    require(np.array_equal(mm(L[1],L[0]),J90) and np.array_equal(mm(L[0],L[1]),J90),'ordinary C2')
    I=eye(2);Z=np.zeros_like(I);J=np.array([[0,2],[1,0]])
    C0=np.block([[J,Z],[Z,-J]])%3
    cases={}
    for x,y,z in product(range(3),repeat=3):
        X=np.array([[x,y],[y,z]]);S=np.block([[I,X],[Z,I]])%3
        C=S@C0@inv3(S)%3
        H1,J9,r=kernel(C,1);H2,_,_=kernel(C,2)
        require(np.array_equal(mm(H2,H1),J9) and np.array_equal(mm(H1,H2),J9),'canonical Weil C2')
        cases.setdefault(r,(H1,H2,J9))
    rng=np.random.default_rng(31127); checks=0
    for r,(H1,H2,J9) in sorted(cases.items()):
        # Right coefficient columns use the transpose of the opposite left phase.
        for first,second in ((0,1),(1,0)):
            H=(H1,H2)[second].T; Hr=(H1,H2)[first].T
            V=eye(90);V=(V+np.triu(rng.integers(0,P,(90,90)),1))%P
            # Each column is an actual fixture vector |0> tensor v.
            full=np.zeros((9,90,90),dtype=np.int64);full[0]=V
            moved=np.einsum('ij,jkl->ikl',H,full)%P
            moved=np.einsum('ij,kjl->kil',L[first],moved)%P
            raw=moved[0]; require(np.array_equal(raw,H[0,0]*mm(L[first],V)%P),'raw sandwich')
            derived=echelon_columns(raw);coord=mm(inverse(derived),raw)
            require(np.array_equal(mm(derived,coord),raw),'derived basis inverse')
            back=Hr[0,0]*mm(L[second],derived)%P
            backcoord=mm(inverse(V),back)
            require(np.array_equal(mm(backcoord,coord),H[0,0]*Hr[0,0]*mm(inverse(V),mm(J90,V))%P),'reverse C2 sandwich')
            require(np.array_equal(mm(L[second],L[first]),J90),'normalized opposite phase')
            checks+=4
    require(0 in cases and len(cases)>1,'nontrivial tested chart')
    shifted=np.roll(eye(9),1,axis=0)
    try:echelon_columns(shifted[0,0]*eye(90))
    except ValueError:rejected=True
    else:rejected=False
    require(rejected,'affine translated negative control')
    return {'ranks':sorted(cases),'signed_transport_checks':checks,'affine_control_rejected':rejected}

if __name__=='__main__':print(run())
