#!/usr/bin/env python3
"""BR53: actual BR29 zero-speed Bianchi source-factor and refusal witness.

Source owners: check_hopf369_br_curvature_energy.carrier (35 bulk,9 wall),
BR29 projected subsidiary connection identities. The exact algebra is:

 P0 = I-A_n(5A_n-4A_n^3), rank P0=9, P0 A_n=0
 P0(A_i J-J B_i)=0 [three tangent directions]
 P0(K_ext+J R)=0 [physical wall source exchange].

Each is a necessary factorization of the *original* constrained Weyl/wall
source through its matching wall dynamics, not an unrelated 2x2 toy.
A nonzero P0 F in an independent physical metric source remains a real
Bianchi obligation and is rejected, even when the homogeneous identities
hold. A moving frame needs a compatible connection Omega, not just P(t).

--part small|physical; physical calls the original heavy 35D carrier.
No proof of variable Einstein–Israel subsidiary propagation is asserted.
"""
import argparse
import sympy as s

def transport_and_refusal(P0):
    n=P0.rows;I=s.eye(n);Q0=I-P0
    assert P0*P0==P0
    # Independent source derivative through the true kernel split.
    iu=next(i for i in range(n) if P0[:,i]!=s.zeros(n,1))
    iq=next(i for i in range(n) if Q0[i,:]!=s.zeros(1,n))
    K=P0[:,iu]*Q0[iq,:]
    assert K*K==s.zeros(n) and P0*K==K and K*P0==s.zeros(n)
    t=s.Symbol("time",real=True)
    S=I+t*K;Si=I-t*K
    P=S*P0*Si
    assert P*P==P and P==P0-t*K
    fbad=S*P0[:,iu]
    fgood=S*Q0[:,iq]
    assert P*fgood==s.zeros(n,1)
    assert P*fbad!=s.zeros(n,1)
    u0=Q0[:,iq]+P0[:,iu]
    u1=Q0[:,iq]+P0[:,iu]
    u=S*(u0+t*u1)
    cov=lambda x:x.diff(t)-K*x
    assert (cov(P*u)-P*cov(u)).applyfunc(s.expand)==s.zeros(n,1)
    # Real source matching is the additional witness P*F==0.
    assert P*cov(u)!=s.zeros(n,1)
    return True

def small():
    transport_and_refusal(s.diag(0,1,1))
    # Geometry-forward factorization: if B is a physical wall constraint,
    # a source A factors through B iff ker(B) subset ker(A).
    B=s.Matrix([[1,1,0],[0,1,1]])
    A=s.Matrix([[2,3,1],[1,2,1]])
    T=s.Matrix([[2,1],[1,1]])
    assert T*B==A
    n=B.nullspace()[0]
    assert A*n==s.zeros(2,1)
    bad=A+s.Matrix([[1,0,0],[0,0,0]])
    assert bad*n!=s.zeros(2,1)
    print("PASS BR53 exact moving projector, source refusal, and bidirectional wall factorization")

def physical():
    from check_hopf369_br_curvature_energy import carrier,P,eta
    C,V,X,G,Y,H,J,A,B,R,W,m=carrier()
    An=A[3]
    AP=5*An-4*An**3
    P0=s.eye(35)-An*AP
    assert P0.rank()==9
    assert P0*P0==P0 and P0*An==s.zeros(35)
    assert G*P0==P0.T*G
    for i in range(3):
        assert P0*(A[i]*J-J*B[i])==s.zeros(35,9)
    # Original full 100-component Maxwell generators; never project
    # before building the physical Kext. Keep all 10 bivector channels.
    pairs=P
    def gen(a):
        T=s.zeros(10)
        for i,(b,c) in enumerate(pairs):
            for k,(d,e) in enumerate(pairs):
                def unit(v,w):
                    return 1 if (v,w)==(d,e) else -1 if (v,w)==(e,d) else 0
                T[i,k]=((eta[a]*unit(4,c) if b==a else
                         -unit(a,c) if b==4 else 0)
                        +(eta[a]*unit(b,4) if c==a else
                         -unit(b,a) if c==4 else 0))
        return s.kronecker_product(T,s.eye(10))+s.kronecker_product(s.eye(10),T)
    LL=[gen(a) for a in range(4)]
    proj=G.inv()*X.T
    M=[]
    for i in range(1,5):
        L=s.zeros(10)
        for k in range(1,5):
            if k==i:continue
            e=P.index((0,k));b=P.index(tuple(sorted((i,k))))
            L[e,b]=L[b,e]=1 if i<k else -1
        M.append(s.kronecker_product(L,s.eye(10)))
    raw=sum((M[i-1]*LL[i] for i in range(1,4)),s.zeros(100))-LL[0]
    Kext=proj*raw*X
    assert P0*(Kext+J*R)==s.zeros(35)
    # Do not erase the rank-nine zero-speed source just because its
    # normal derivative projection vanished.
    transport_and_refusal(P0)
    print("PASS BR53 ORIGINAL 35D BR29, 9 zero modes, three tangent factorizations")
    print("PASS original Kext+JR cancellation; independent source NOT automatically constrained")

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--part",choices=["small","physical"],default="small")
    a=p.parse_args()
    (small if a.part=="small" else physical)()

if __name__=="__main__":main()
