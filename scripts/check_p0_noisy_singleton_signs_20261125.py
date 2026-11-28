"""Direct Clay P0: noisy marked singleton signs, exact reverse decoding.
Classical Reed-Solomon/Hadamard concatenation and Welch-Berlekamp decoding.
No source-side predictor is supplied; exhaustive witnesses are test fixtures only.
"""
from random import Random
from itertools import product
from sympy import nextprime

def chart(n):
    assert n >= 1
    p = int(nextprime(4*n))
    q = 1 << (p-1).bit_length()
    return p,q

def evaluate(coefs,a,p):
    v=0
    for c in reversed(coefs):
        v=(v*a+c)%p
    return v

def bit(v,b):
    return (v&b).bit_count()&1

def encode(x):
    p,q=chart(len(x))
    return [bit(evaluate(x,a,p),b) for a in range(p) for b in range(q)]

def linear_solve(rows,k,p):
    r=0
    piv=[]
    for j in range(k):
        t=next((i for i in range(r,len(rows)) if rows[i][j]%p),None)
        if t is None:
            continue
        rows[r],rows[t]=rows[t],rows[r]
        z=pow(rows[r][j]%p,-1,p)
        rows[r]=[v*z%p for v in rows[r]]
        for i in range(len(rows)):
            if i!=r and rows[i][j]:
                z=rows[i][j]
                rows[i]=[(a-z*b)%p for a,b in zip(rows[i],rows[r])]
        piv.append(j)
        r+=1
    if any(not any(row[:k]) and row[k] for row in rows):
        return None
    ans=[0]*k
    for i,j in enumerate(piv):
        ans[j]=rows[i][k]
    return ans

def outer_decode(y,n,p):
    e=(p-n)//2
    k=n+2*e
    rows=[]
    for a,v in enumerate(y):
        powers=[1]
        for _ in range(max(n+e-1,e)):
            powers.append(powers[-1]*a%p)
        rows.append(powers[:n+e]+[(-v*z)%p for z in powers[:e]]+[v*powers[e]%p])
    sol=linear_solve(rows,k,p)
    if sol is None:
        return None
    R=sol[:n+e]
    E=sol[n+e:]+[1]
    P=[0]*n
    for i in range(n-1,-1,-1):
        P[i]=R[i+e]
        for j,v in enumerate(E):
            R[i+j]=(R[i+j]-P[i]*v)%p
    if any(R) or any(v not in (0,1) for v in P):
        return None
    if sum(evaluate(P,a,p)!=v for a,v in enumerate(y))>e:
        return None
    return tuple(P)

def decode(z,n):
    p,q=chart(n)
    if len(z)!=p*q or any(v not in (0,1) for v in z):
        return None
    y=[]
    for a in range(p):
        row=z[a*q:(a+1)*q]
        y.append(min(range(p),key=lambda v:sum(x!=bit(v,b) for b,x in enumerate(row))))
    return outer_decode(y,n,p)

def satisfies(F,x):
    return all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F)

def verified(F,z,n):
    x=decode(z,n)
    return x if x is not None and satisfies(F,x) else None

def compile_chart(F,n):
    """One-hot modular recurrence and OR gates; parsimonious width<=3 CNF.
    Return clauses, topologically ordered gate receipts, marked code coordinates.
    """
    p,q=chart(n)
    clauses=list(F)
    gates=[]
    def gate(op,*ins):
        j=n+len(gates)+1
        gates.append((op,ins))
        if op=="false": clauses.append((-j,))
        elif op=="true": clauses.append((j,))
        elif op=="and":
            a,b=ins
            clauses.extend([(-j,a),(-j,b),(j,-a,-b)])
        elif op=="or":
            a,b=ins
            clauses.extend([(j,-a),(j,-b),(-j,a,b)])
        else: raise ValueError(op)
        return j
    zero=gate("false")
    one=gate("true")
    marked=[]
    for a in range(p):
        state=[one]+[zero]*(p-1)
        for i in range(n):
            w=pow(a,i,p)
            u=i+1
            state=[gate("or",gate("and",-u,state[v]),gate("and",u,state[(v-w)%p])) for v in range(p)]
        for b in range(q):
            z=zero
            for v in range(p):
                if bit(v,b):
                    z=gate("or",z,state[v])
            # fresh marked coordinate, even for identical/constant output
            marked.append(gate("or",z,zero))
    return clauses,gates,marked

def lift(x,gates):
    out=list(x)
    def read(l):
        return out[abs(l)-1]^int(l<0)
    for op,ins in gates:
        if op=="false": v=0
        elif op=="true": v=1
        elif op=="and": v=read(ins[0])&read(ins[1])
        else: v=read(ins[0])|read(ins[1])
        out.append(v)
    return tuple(out)

def main():
    rng=Random(85)
    clean=noisy=burst=compiled=off=0
    for n in range(1,9):
        p,q=chart(n)
        xs=list(product((0,1),repeat=n)) if n<=5 else [tuple(rng.randrange(2) for _ in range(n)) for _ in range(8)]
        for x in xs:
            z=encode(x)
            assert decode(z,n)==x
            clean+=1
            # full allowed budget, arbitrary dispersed errors
            zz=z.copy()
            for i in rng.sample(range(p*q),p*q//16): zz[i]^=1
            assert decode(zz,n)==x
            noisy+=1
            # concentrate errors on inner rows, crossing their quarter-distance
            zz=z.copy()
            bad=(p*q//16)//(q//4+1)
            for a in rng.sample(range(p),bad):
                for b in rng.sample(range(q),q//4+1): zz[a*q+b]^=1
            assert decode(zz,n)==x
            burst+=1
            F=[(i+1 if v else -i-1,) for i,v in enumerate(x)]
            y=verified(F,encode(tuple(1-v for v in x)),n)
            assert y is None
            off+=1
    for n in range(1,5):
        F=[(1,)] if n==1 else [(1,-2)]
        G,gates,marked=compile_chart(F,n)
        assert all(len(c)<=3 for c in G)
        for x in product((0,1),repeat=n):
            X=lift(x,gates)
            assert satisfies(G,X)==satisfies(F,x)
            assert [X[j-1] for j in marked]==encode(x)
            compiled+=1
    # Small-support collisions in the packed 2-adic scalar, even with verified anchor.
    collisions=0
    for n in range(3,65):
        m=1<<(n+2)
        tags=(1,5,9,m-15)
        assert len(set(tags))==4 and all(t%4==1 for t in tags)
        assert sum(tags)%m==0
        anchor=13
        assert anchor not in tags and (anchor+sum(tags))%m==anchor
        collisions+=1
    print(dict(clean=clean,noisy=noisy,burst=burst,compiled=compiled,invalid_candidates=off,scalar_collision_arities=collisions))

if __name__=="__main__":
    main()
