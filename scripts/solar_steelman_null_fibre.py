"""Exact modular rank witness for the actual material null-fibre constraint."""
import pickle
import sympy as S

def run(m,a):
    B=m['B'];cols=[]
    for ids,r,c in a['models']:
        for w in (1,2):
            for x in r[w]:
                v=S.zeros(B.cols,1)
                for i,j in enumerate(ids):v[j]=x[i]
                cols.append(v)
    F=S.Matrix.hstack(*cols);A=B.col_join(F.T)
    prime=1000000007
    assert S.isprime(prime)
    rows=[]
    for row in A.tolist():
        z=[]
        for x in row:
            p,q=map(int,S.Rational(x).as_numer_denom())
            assert q%prime
            z.append(p*pow(q,-1,prime)%prime)
        rows.append(z)
    rank=0
    for col in range(A.cols):
        k=next((k for k in range(rank,len(rows)) if rows[k][col]),None)
        if k is None:continue
        rows[rank],rows[k]=rows[k],rows[rank]
        pivot=rows[rank];inv=pow(pivot[col],-1,prime)
        for k in range(rank+1,len(rows)):
            r=rows[k];factor=r[col]*inv%prime
            if factor:rows[k]=[(x-factor*y)%prime for x,y in zip(r,pivot)]
        rank+=1
    assert rank==A.cols
    print('PASS rational stacked material constraint full column rank',rank,'prime',prime,'shape',A.shape,flush=True)
    print('ker B intersect common local-force annihilator = {0}; no static invisible material shift',flush=True)

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--metric',required=True);p.add_argument('--mediator',required=True);a=p.parse_args()
    with open(a.metric,'rb') as f:m=pickle.load(f)
    with open(a.mediator,'rb') as f:b=pickle.load(f)
    run(m,b)
