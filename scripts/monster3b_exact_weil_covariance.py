#!/usr/bin/env python3
"""Exact original TOE Weyl covariance, parity and canonical scalar receipt.
No actual ambient Monster vector action is inferred from this model check.
"""
import argparse, hashlib, json
from fractions import Fraction as F
from pathlib import Path
import numpy as np
from toe_cyclotomic_operator import compile_shape, columns, points
from monster3b_atlas_generation_certificate import source, inv, require

# Same alternating form as the existing ATLAS actual D4 owner.
FORM='''002122102121
001121022112
120000021212
220000201221
110000221021
120000212120
200111002221
011012002111
112221110201
221102121020
122111120101
211220222020'''
P=31
ROOTS=((1,0),(0,1),(-1,-1))

def mul(a,b):
    x,y=a;u,v=b
    return x*u-y*v,x*v+y*u-y*v

def power(a,n):
    if n<0:
        x,y=a;d=x*x-x*y+y*y;a=(F(x-y,d),F(-y,d));n=-n
    out=(F(1),F(0))
    for _ in range(n):out=mul(out,a)
    return out

def red(q):
    def f(x):
        x=F(x);return x.numerator*pow(x.denominator,-1,P)%P
    return (f(q[0])+5*f(q[1]))%P

def det(A):
    A=np.asarray(A,dtype=np.int64).copy()%P;d=1
    for i in range(len(A)):
        nz=np.flatnonzero(A[i:,i]);require(len(nz)>0,'singular parity block')
        j=i+int(nz[0]);A[[i,j]]=A[[j,i]]
        if i!=j:d=-d
        a=int(A[i,i]);d=d*a%P
        A[i+1:]=(A[i+1:]-(A[i+1:,i]*pow(a,-1,P)%P)[:,None]*A[i])%P
    return d%P

def atlas_chart(root):
    C,D=source(root);J=np.array([[int(c) for c in row] for row in FORM.splitlines()])
    require(np.array_equal(C.T@J@C%3,-J%3) and np.array_equal(D.T@J@D%3,J),'original form residual')
    work=list(np.eye(12,dtype=np.int64));a=[];b=[]
    while work:
        u=work.pop(0);j=next(i for i,v in enumerate(work) if u@J@v%3)
        v=work.pop(j)
        v=v*(u@J@v%3)%3
        work=[(w-(w@J@v)*u+(w@J@u)*v)%3 for w in work];a.append(u);b.append(v)
    S=np.column_stack(a+b);Si=inv(S)
    J0=np.block([[np.zeros((6,6),dtype=int),np.eye(6,dtype=int)],[-np.eye(6,dtype=int),np.zeros((6,6),dtype=int)]])
    require(np.array_equal(S.T@J@S%3,J0%3),'chart form residual')
    return Si@C@S%3,Si@D@S%3

def labels(A,lam,s):
    R=compile_shape(A,lam,s);n=len(R['origin']);N=3**n
    require(not any(R['origin']) and R['constant']==0,'nonzero affine vacuum origin')
    R['scalar']=[1,0,1];Q=np.full((N,N),-1,dtype=np.int8)
    for j,y,(a,b) in columns(R):
        require(len(np.unique(y))==len(y)==3**R['rank'],'support rank residual')
        for k,(p,t) in enumerate(ROOTS):Q[y[(a==p)&(b==t)],j]=k
    require(np.all(np.count_nonzero(Q>=0,axis=0)==3**R['rank']) and Q[0,0]==0,'raw unit vacuum residual')
    return Q,R['rank']

def shift(q,e):return np.where(q<0,-1,(q+e)%3)

def covariance(Q,A,lam,s):
    n=len(A)//2;X=points(n);p=3**np.arange(n-1,-1,-1);sout=s*lam%3
    for j,v in enumerate(np.eye(2*n,dtype=np.int64)):
        a,b=v[:n],v[n:];w=A@v%3;c,d=w[:n],w[n:]
        src=((X+a)%3)@p;dst=((X+c)%3)@p
        lhs=shift(Q[:,src],s*(X@b)[None,:])
        rhs=np.empty_like(Q);rhs[dst,:]=shift(Q,sout*(X@d+2*(c@d))[:,None])
        require(np.array_equal(lhs,rhs),f'exact Weyl covariance residual axis {j} phase {s}')
    neg=(-X%3)@p
    require(np.array_equal(Q[neg,:],Q[:,neg]),'exact parity residual')
    return neg

def canonical_record(Q,r,neg):
    # Every entry is in Z[zeta,1/3]; exact covariance plus Schur and
    # column norm prove Delta^-r K unitary. Its two parity determinants
    # are norm-one S-units, hence mu6. The following finite computation
    # selects that exact ratio, not a general lift of a modular matrix.
    scale=power((F(1),F(2)),-r);values=np.array([1,5,25,0]);K=values[Q]*red(scale)%P
    reps=np.flatnonzero(np.arange(len(neg))<neg);even=np.r_[0,reps]
    E=K[np.ix_(even,even)].copy();E[:,1:]=(E[:,1:]+K[np.ix_(even,neg[reps])])%P
    O=(K[np.ix_(reps,reps)]-K[np.ix_(reps,neg[reps])])%P
    ratio=det(E)*pow(det(O),-1,P)%P
    lifts=[(sgn*a,sgn*b) for a,b in ROOTS for sgn in (1,-1) if red((sgn*a,sgn*b))==ratio]
    require(len(lifts)==1,'determinant ratio not mu6')
    c=mul(power(lifts[0],-1),scale)
    return {'rank':r,'weyl_axes':12, 'even_dimension':len(even),'odd_dimension':len(reps),
            'det_ratio_Qzeta3':[str(x) for x in lifts[0]],'det_ratio_mod31':ratio,
            'normalized_vacuum_Qzeta3':[str(x) for x in c],'normalized_vacuum_mod31':red(c),'zero_affine_vacuum_unit_verified':True}

def run(C,D,model=None):
    records={};negative=0
    for g,A,lam in (('C',C,2),('D',D,1),('E',C@D@inv(C)%3,1)):
        for s in (1,2):
            Q,r=labels(A,lam,s);neg=covariance(Q,A,lam,s)
            rec=canonical_record(Q,r,neg);records[f'{g}:{s}']=rec
            if model:
                old=model['generators'][f'{g}:{s}']
                require(all(old[k]==v for k,v in rec.items() if k not in ('weyl_axes','even_dimension','odd_dimension')),'canonical receipt scalar mismatch')
            bad=Q.copy();bad[0,0]=1
            try:covariance(bad,A,lam,s)
            except ValueError:negative+=1
            else:raise ValueError('corrupted kernel accepted')
    return {'status':'EXACT_SIGNED_WEYL_COVARIANCE_AND_PARITY','generators':records,'exact_weyl_axis_equations':72,'exact_parity_equations':6,'negative_controls':negative,'canonical_receipt_compared':model is not None,'actual_ambient_Monster_action_executed':False}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[1]);p.add_argument('--cover',type=Path);p.add_argument('--model',type=Path);p.add_argument('--out',type=Path);a=p.parse_args()
    if a.model and not a.cover:p.error('model comparison needs literal cover')
    m=None
    if a.cover:
        c=json.loads(a.cover.read_text());require(c.get('actual_mmgroup_used') is True,'literal cover required')
        for g,lam in (('C',2),('D',1)):
            q=c['canonical_'+g];require(q['central_multiplier_mod3']==lam and not any(q['affine_ell_F3']),'literal affine/phase residual')
        C,D=(np.array(c['canonical_'+g]['matrix_F3'],dtype=np.int64) for g in ('C','D'))
        if a.model:
            m=json.loads(a.model.read_text());require(m['status']=='CANONICAL_MODEL_SIGNED_SECTION' and m['source_chart']=='literal corrected MM quotient' and all(m[k]==c[k] for k in ('canonical_C_word','canonical_D_word','central_cover_relators')) and m['original_E_source_blob_sha']==c['original_source_blob_sha'],'literal model provenance')
    else:C,D=atlas_chart(a.root)
    r=run(C,D,m);r['source_chart']='literal cover matrices' if a.cover else 'pinned ATLAS chart';r['inputs_sha256']={str(x):hashlib.sha256(x.read_bytes()).hexdigest() for x in (a.cover,a.model) if x}
    if a.out:a.out.parent.mkdir(parents=True,exist_ok=True);a.out.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(r,indent=2))
if __name__=='__main__':main()
