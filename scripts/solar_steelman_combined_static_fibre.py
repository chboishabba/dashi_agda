"""Static combined material/magnetic fibre and charge-continuity audit.
Exact rational constraints on original enriched Whitney geometry.
"""
import sympy as S

def modrank(A,p=1000000007):
    assert S.isprime(p)
    rows=[]
    for row in A.tolist():
        rr=[]
        for x in row:
            n,d=map(int,S.Rational(x).as_numer_denom())
            if d%p==0:raise ValueError("choose a different prime")
            rr.append(n*pow(d,-1,p)%p)
        rows.append(rr)
    rank=0
    for j in range(A.cols):
        k=next((k for k in range(rank,len(rows)) if rows[k][j]),None)
        if k is None:continue
        rows[rank],rows[k]=rows[k],rows[rank];v=rows[rank];inv=pow(v[j],-1,p)
        for k in range(rank+1,len(rows)):
            q=rows[k];factor=q[j]*inv%p
            if factor:rows[k]=[(x-factor*y)%p for x,y in zip(q,v)]
        rank+=1
        if rank==len(rows):break
    return rank

def run(m,a,exact_null=False):
    d=m['d'];G,C,N,B=d['G'],d['C'],d['N'],m['B']
    assert C*G==S.zeros(C.rows,G.cols)
    rg,rc=modrank(G),modrank(C)
    # Incidence gradient annihilates constants, so rank G<=cols-1.
    assert G*S.ones(G.cols,1)==S.zeros(G.rows,1)
    if rg==G.cols-1 and rc==G.rows-rg:
        print("PASS exact im C^T = ker G^T",rc,flush=True)
    else:raise RuntimeError("topology not certified by modular lower bounds")
    cols=[]
    for ids,r,_ in a['models']:
        for w in (1,2):
            for v in r[w]:
                f=S.zeros(B.cols,1)
                for k,j in enumerate(ids):f[j]=v[k]
                cols.append(f)
    F=S.Matrix.hstack(*cols)
    # A constant z perturbation can be cancelled by a magnetic shift:
    # C^T N delta b = B delta z. It is invisible to store dynamics
    # iff F^T delta z=0. Do NOT require B delta z=0.
    A=(G.T*B).col_join(F.T);rank=modrank(A)
    print("combined static constraint",A.shape,"modular rank lower bound",rank,flush=True)
    if rank==A.cols:
        print("PASS no combined static material shift, only magnetic invariant shifts",flush=True)
    elif exact_null:
        Z=A.nullspace()
        for z in Z:
            assert A*z==S.zeros(A.rows,1)
            b,params=(C.T*N).gauss_jordan_solve(B*z)
            b=b.subs({v:0 for v in params})
            assert C.T*N*b==B*z and F.T*z==S.zeros(F.cols,1)
        print("EXACT combined material static nullity",len(Z),flush=True)
    else:
        print("OPEN rank upper bound / exact nullspace; modular rank alone is insufficient",flush=True)
    # Charge continuity follows directly by left multiplication of Ampere.
    # Qfield=G^T M E; Qmaterial'=G^T B z; terminal charges from q'=i.
    # Qfield+Qmaterial-G^T ts^T q+G^T tr^T Q is constant.
    assert G.T*C.T==S.zeros(G.cols,C.rows)
    print("PASS exact charge continuity incidence; material charge requires history or explicit accumulator",flush=True)
    return rank

if __name__=="__main__":
    import argparse,pickle
    p=argparse.ArgumentParser();p.add_argument("--metric",required=True);p.add_argument("--mediator",required=True)
    p.add_argument("--exact-null",action="store_true");x=p.parse_args()
    with open(x.metric,"rb") as f:m=pickle.load(f)
    with open(x.mediator,"rb") as f:a=pickle.load(f)
    run(m,a,x.exact_null)
