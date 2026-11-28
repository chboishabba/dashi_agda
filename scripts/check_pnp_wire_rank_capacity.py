"""Exact finite wire-feature rank and sharing negative controls.
Explicit output obligations are not automatically SAT obligations.
"""
from itertools import combinations

def rank2(vectors):
    piv={}
    for x in vectors:
        while x:
            i=x.bit_length()-1
            if i in piv:x^=piv[i]
            else:piv[i]=x;break
    return len(piv)

def features(n):
    X=range(1<<n);one=(1<<(1<<n))-1
    inputs=tuple(sum(((x>>i)&1)<<x for x in X) for i in range(n))
    base=(one,)+inputs;gates=tuple(a&b for a,b in combinations(inputs,2))
    r=rank2(base);last=r
    for j in range(len(gates)):
        now=rank2(base+gates[:j+1]);assert last<=now<=last+1;last=now
    assert r==n+1 and last==r+len(gates)
    return n,r,len(gates),last

def inner_product(m):
    N=1<<m;rows=[]
    for x in range(N):
        row=0
        for y in range(N):
            # m ANDs and m-1 XORs (each XOR is five AND/OR/NOT gates).
            terms=[((x>>i)&1)&((y>>i)&1) for i in range(m)]
            bit=terms[0]
            for t in terms[1:]:bit^=t
            assert bit==(x&y).bit_count()%2
            row|=bit<<y
        rows.append(row)
    # Sign matrix entries (-1)^bit: distinct rows are orthogonal over Q.
    assert all((a^b).bit_count()==N//2 for a,b in combinations(rows,2))
    return m,N,6*m-5,N*(N-1)//2

def main():
    print(dict(explicit_outputs=[features(n) for n in range(2,9)],
               inner_product=[inner_product(m) for m in range(1,9)]))
if __name__=='__main__':main()
