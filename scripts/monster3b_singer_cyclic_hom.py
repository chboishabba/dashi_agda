#!/usr/bin/env python3
"""Source-indexed C13 orbit Hom solver, positive phase then signed transport.

Lindsey/ATLAS source matrices; Singer offsets from #1291.  No identification
of the 3D Griess Singer action with the 12D Monster quotient is assumed.
Only genuine packet consumers may assert actual Monster attachment.
"""
import numpy as np
from monster3b_actual_projective_sym2_intertwiner import inverse, symmetric_square, singleton_nullspace
from monster3b_lindsey_actual_mod31_join import source_matrices, dual, bd, power, mm
P=31
W="DEdeDeDEDEdedEd"
OFFSETS=(0,6,10,11)

def require(x,msg):
    if not x:raise ValueError(msg)
def ident(n):return np.eye(n,dtype=np.int64)
def eq(A,B):return np.array_equal(A%P,B%P)
def word(ops,w):
    # Right MMV action on coefficient columns: first letter acts first.
    A=ident(len(ops["D"]))
    for t in w:A=mm(ops[t],A)
    return A
def wheel(ops,n):
    G=power(word({**ops,"d":power(ops["D"],2),"e":power(ops["E"],2)},W),3)
    I=ident(n);require(eq(power(G,13),I) and not eq(G,I),"source order13")
    pp=[power(G,k) for k in range(13)]
    J=sum(pp)%P;B=sum(pp[k] for k in OFFSETS)%P
    Bt=sum(pp[-k%13] for k in OFFSETS)%P
    Bi=(pow(3,-1,P)*Bt-pow(12,-1,P)*J)%P
    require(eq(mm(B,Bt),3*I+J) and eq(mm(B,Bi),I) and eq(mm(Bi,B),I),"Singer inverse")
    require(eq(mm(J,J),13*J),"collective projector")
    rank=rank_mod(J)
    require(rank=={12:0,78:6}[n],"source collective rank")
    return G,rank

def rank_mod(A):
    A=np.array(A,dtype=np.int64)%P
    r=0
    for j in range(A.shape[1]):
        k=next((i for i in range(r,len(A)) if A[i,j]),None)
        if k is None:continue
        A[[r,k]]=A[[k,r]];A[r]=A[r]*pow(int(A[r,j]),-1,P)%P
        A[r+1:]=(A[r+1:]-A[r+1:,j,None]*A[r])%P
        r+=1
        if r==len(A):break
    return r

def orbit(ops):
    n=len(ops["D"]);G,k=wheel(ops,n);ops={**ops,"G":G}
    vectors=[];words=[];rows=[];piv=[]
    def accept(v,w):
        a=v.copy()%P
        for j,r in zip(piv,rows):a=(a-a[j]*r)%P
        nz=np.flatnonzero(a)
        if not len(nz):return
        j=int(nz[0]);rows.append(a*pow(int(a[j]),-1,P)%P)
        piv.append(j);vectors.append(v.copy());words.append(w)
    v=ident(n)[:,0]
    for j in range(13):
        accept(v,"G"*j);v=G@v%P
    initial=len(vectors)
    for i in range(n):
        if len(vectors)==n or i>=len(vectors):break
        for g in ("G","D","E"):
            accept(ops[g]@vectors[i]%P,words[i]+g)
            if len(vectors)==n:break
    require(len(vectors)==n,"source orbit not cyclic")
    return np.column_stack(vectors),words,{"dimension":n,"collective_rank":k,
        "initial_wheel_rank":initial,"max_macro_word_length":max(map(len,words))}

def solve(source,target):
    n=len(source["D"])
    B,words,receipt=orbit(source);Binv=inverse(B)
    G,_=wheel(target,n);ops={**target,"G":G}
    Wt=np.stack([word(ops,w) for w in words])
    # Unknown only the image y of the first source vector, not n*n
    # entries of an intertwiner.  Generator closure is exhaustive.
    rows=[]
    for g in ("D","E"):
        M=mm(Binv,mm(source[g],B))
        for i in range(n):
            rows.append((mm(target[g],Wt[i])-np.tensordot(M[:,i],Wt,axes=1))%P)
    y=singleton_nullspace(np.concatenate(rows,axis=0))
    require(y is not None,"cyclic Hom seed nullity not one")
    F=mm(np.column_stack([T@y%P for T in Wt]),Binv)
    inverse(F)
    require(all(eq(mm(F,source[g]),mm(target[g],F)) for g in ("D","E")),
            "source cyclic Hom generator equation")
    receipt.update(seed_unknowns=n,seed_nullity=1,words=words)
    return F,receipt

def direct_signed_compare(A,H,data):
    z=np.diag([5]*12+[25]*12)
    Q=power(word({"D":A["D"],"C":A["C"]},"CDCDD"),7)
    q=next((k for k in range(3) if eq(Q,power(z,k))),None)
    require(q is not None,"actual Q7 not central")
    T=source_matrices(data,q)
    U={g:dual(T[g],g=="C") for g in T}
    transports={};receipts={}
    for n,src,dst in ((12,T,A),(78,U,H)):
        # Fp points ordinary -> actual. Opposite phase derived, no search.
        Fp,rec=solve({g:src[g][:n,:n] for g in ("D","E")},
                     {g:dst[g][:n,:n] for g in ("D","E")})
        Fm=mm(mm(dst["C"][n:,:n],Fp),inverse(src["C"][n:,:n]))
        F=bd(Fp,Fm)
        require(all(eq(mm(F,src[g]),mm(dst[g],F)) for g in ("C","D","E")),
                "full signed cyclic source correspondence")
        transports[n]=inverse(F);receipts[n]=rec
    F,J=transports[12],transports[78]
    # Existing consumer convention: G actual78 -> Sym2(actual12 dual).
    G={s:mm(symmetric_square(F[i*12:(i+1)*12,i*12:(i+1)*12].T),
            J[i*78:(i+1)*78,i*78:(i+1)*78]) for i,s in enumerate((1,2))}
    return q,F,J,G,receipts

def source_selftest(data):
    rng=np.random.default_rng(20261125);checks=0;negative=0;receipts={}
    def hidden(n):
        while True:
            A=rng.integers(0,P,(n,n),dtype=np.int64)
            try:inverse(A);return A
            except ValueError:pass
    for q in range(3):
        T=source_matrices(data,q);U={g:dual(T[g],g=="C") for g in T}
        X=bd(hidden(12),hidden(12));Y=bd(hidden(78),hidden(78))
        A={g:mm(mm(X,T[g]),inverse(X)) for g in T}
        H={g:mm(mm(Y,U[g]),inverse(Y)) for g in U}
        found,F,J,G,r=direct_signed_compare(A,H,data)
        require(found==q,"fixture central phase")
        checks+=6;receipts[q]=r
        wrong=dict(H);wrong["E"]=ident(156)
        try:direct_signed_compare(A,wrong,data)
        except ValueError:negative+=1
        else:raise ValueError("wrong source passed")
    return {"status":"SOURCE_DERIVED_FIXTURES_ONLY","equations":checks,
            "negative_controls":negative,"receipts":receipts}
if __name__=="__main__":
    import json
    from pathlib import Path
    data=json.loads((Path(__file__).resolve().parents[1]/"Docs/support/reference/Monster3BLindseyOrdinaryCD20261124.json").read_text())
    print(json.dumps(source_selftest(data),indent=2))
