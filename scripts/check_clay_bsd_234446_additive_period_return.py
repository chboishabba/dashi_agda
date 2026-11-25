"""Exact finite Fourier identities on original 234446a1 coefficients.
No new cusp symbol evaluation or complex derivative vanishing claimed.
"""
from math import gcd, lcm
import sympy as sp
N=234446
checks=0

def ck(ok):
    global checks
    if not ok: raise AssertionError('additive return control failed')
    checks+=1

def trace(p):
    if p==2:
        return p-sum((y*y+x*y-x**3+x*x+79*x-289)%p==0 for x in range(p) for y in range(p))
    squares={x*x%p for x in range(1,p)}
    return sum(0 if (d:=(4*x**3-3*x*x-316*x+1156)%p)==0 else 1-2*(d in squares) for x in range(p))

def coeff(n):
    out=1
    for p,e in sp.factorint(n).items():
        p=int(p); a=trace(p); u,v=1,a
        for _ in range(1,e): u,v=v,a*v-(0 if N%p==0 else p*u)
        out*=v
    return out

M=257
cs=[0]+[coeff(n) for n in range(1,M+1)]
ck(cs[1]==1 and cs[5]==-4 and cs[11]==-6)

def reduce(v,p):
    q=len(v);h=q//p
    return [v[i+j*h]-v[i+(p-1)*h] for j in range(p-1) for i in range(h)]

def ramanujan(t,p,q):
    return q-q//p if t%q==0 else -q//p if t%(q//p)==0 else 0

for p,q in ((5,5),(5,25),(5,125),(11,11),(11,121)):
    h=q//p; U=[a for a in range(q) if gcd(a,q)==1]
    J={a:-pow(N*a,-1,q)%q for a in U}
    ck(all(J[J[a]]==a and J[-a%q]==-J[a]%q for a in U))
    L=min(M,2*q+7); D=lcm(*range(1,L+1))
    # Two distinct rational radial parameters, with common denominator cleared.
    # These are exact coefficient tests, NOT the actual exponential heights.
    W=[0]+[cs[m]*(D//m)*3**m*4**(L-m)*3**L for m in range(1,L+1)]
    V=[0]+[cs[m]*(D//m)*2**m*3**(L-m)*4**L for m in range(1,L+1)]
    for k in sorted({1,2,3,p,p+1}):
        direct=[0]*q; reflected=[0]*q
        # Original path-side cosine expansion, multiplied by two.
        for a in U:
            for m in range(1,L+1):
                direct[((m-k)*a)%q]+=W[m]
                direct[((-m-k)*a)%q]+=W[m]
                reflected[(m*J[a]-k*a)%q]+=V[m]
                reflected[(-m*J[a]-k*a)%q]+=V[m]
        # Independently contract direct frequencies by the Ramanujan formula.
        expected=sum(W[m]*(ramanujan(m-k,p,q)+ramanujan(-m-k,p,q)) for m in range(1,L+1))
        ck(reduce(direct,p)==[expected]+[0]*(q-h-1))
        # Reflected contribution: exact cyclotomic Kloosterman buckets.
        dual=[0]*q; invN=pow(N,-1,q)
        for m in range(1,L+1):
            for b in U:
                # Substitute b=-a^-1/N, not the original a coordinate.
                t=k*invN*pow(b,-1,q)
                dual[(t+m*b)%q]+=V[m]
                dual[(t-m*b)%q]+=V[m]
        ck(reduce(reflected,p)==reduce(dual,p))
        if k%p and h>1:
            for a in range(1,h):
                if a%p==0: continue
                v=[0]*q
                for j in range(p):v[-k*(a+j*h)%q]+=1
                ck(not any(reduce(v,p)))
    # Exact even/Fricke-preserving collision for a first additive cosine mode.
    # Analytic equidistribution proves the analogous large-q result for the
    # actual nonconstant Mellin kernel; this finite test is only a mode control.
    roots=[a for a in U if pow(a,p-1,q)==1]
    z=next(a for a in roots if a not in (1,q-1))
    labels={a*pow(1+p,k,q)%q:k for a in roots for k in range(h)}
    def orbit(a): return [a,-a%q,J[a],-J[a]%q]
    def mode(a):
        v=[0]*q
        for b in orbit(a):v[b]+=1;v[-b%q]+=1
        return reduce(v,p)
    collisions=0
    for a in U:
        b=z*a%q
        ck(sorted(labels[x] for x in orbit(a))==sorted(labels[x] for x in orbit(b)))
        collisions+=mode(a)!=mode(b)
    print('p,q',p,q,'original coefficient cutoff',L,'mode collisions',collisions,flush=True)
    ck(collisions>0 or q==p)
print(f'{checks}/{checks} exact controls PASS',flush=True)
