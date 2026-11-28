"""Read-only donor: ExplicitCode729.agda systematic generator (actual encode).
Hyperbolic complement for Q(x)=sum_{i<j} x_i*x_j, over F3.
"""
from itertools import product
from check_pnp_quadratic_phase import gauss

A=((2,0,2,1,1,2),(2,1,1,2,0,2),(2,2,0,2,1,1),(2,2,1,1,2,0),(2,1,2,0,2,1),(0,1,1,1,1,1))
G=tuple(tuple(int(i==j) for j in range(6))+row for i,row in enumerate(A))
def dot(x,y):return sum(a*b for a,b in zip(x,y))%3
def B(x,y):return (sum(x)*sum(y)-dot(x,y))%3
def Q(x):return sum(a*b for i,a in enumerate(x) for b in x[i+1:])%3
def lin(c,M):return tuple(sum(a*v[j] for a,v in zip(c,M))%3 for j in range(12))
E=tuple(tuple(2*int(i==j) for j in range(12)) for i in range(6))
H=tuple(tuple((E[i][j]+sum(G[k][j] for k in range(6) if k!=i))%3 for j in range(12)) for i in range(6))
def encode(a,b):return lin(a+b,G+H)
def decode(x):return tuple(B(x,h) for h in H),tuple(B(g,x) for g in G)
def main():
    assert all(sum(g)%3==0 for g in G)
    for i,j in product(range(6),repeat=2):
        assert dot(G[i],G[j])==B(G[i],G[j])==B(H[i],H[j])==0
        assert B(G[i],H[j])==int(i==j)
    assert all(Q(x)==0 for x in G+H)
    W=list(product(range(3),repeat=6));weights={}
    for a in W:
        x=encode(a,(0,)*6);w=sum(v!=0 for v in x);weights[w]=weights.get(w,0)+1
        assert decode(x)==(a,(0,)*6)
    assert weights=={0:1,6:264,9:440,12:24}
    count=[0]*3
    for a in W:
        for b in W:count[dot(a,b)]+=1
    assert count==[177633,176904,176904]
    P={(i,j):1 for i in range(12) for j in range(i+1,12)}
    assert gauss(P,12,lambda _:None)==(729,0)
    for a,b in zip(W,reversed(W)):
        x=encode(a,b);assert decode(x)==(a,b) and Q(x)==dot(a,b)
    print(dict(weights=weights,hyperbolic_gram_checks=108,message_pairs=len(W)**2,histogram=count,character=729,bidi_samples=len(W),H=H))
if __name__=='__main__':main()
