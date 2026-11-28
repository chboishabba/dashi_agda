import sympy as s
from itertools import combinations

def run(X,G,A):
    I=range(5); P=list(combinations(I,2)); T=list(combinations(I,3)); eta=(-1,1,1,1,1)
    def signed(seq,keys):
        if len(set(seq))!=len(seq):return 0,0
        return keys.index(tuple(sorted(seq))),(-1)**sum(a>b for i,a in enumerate(seq) for b in seq[i+1:])
    C=[]; K=[]; D=s.zeros(50,100)
    for b in I:
        for j,(d,e) in enumerate(P):
            for a in I:
                t,sg=signed((a,d,e),T); p,sg2=signed((a,b),P)
                D[10*b+j,10*t+p]+=eta[a]*sg*sg2
    for k in I:
        c=s.zeros(100,100); z=s.zeros(100,100); w=s.zeros(100,50)
        for i,(a,b,d) in enumerate(T):
            for j in range(10):
                for axis,pair,sg in ((a,(b,d),1),(b,(a,d),-1),(d,(a,b),1)):
                    if axis==k:c[10*i+j,10*P.index(pair)+j]+=sg
        for i,(a,b) in enumerate(P):
            t,sg=signed((k,a,b),T)
            for j in range(10):
                z[10*i+j,10*t+j]+=eta[k]*sg
                if a==k:w[10*i+j,10*b+j]+=1
                if b==k:w[10*i+j,10*a+j]-=1
        C.append(c*X); K.append(G.inv()*X.T*(z+w*D))
    for a in I:
        assert K[a]*C[a]==eta[a]*s.eye(35)
        for b in range(a):assert K[a]*C[b]+K[b]*C[a]==s.zeros(35)
    print('PASS 15 exact coefficient identities K(xi) C(xi)=q(xi) I',flush=True)
    # Normal derivative extraction and constraint projector.
    L=K[4]; Q=s.eye(100)-C[4]*L
    assert L*C[4]==s.eye(35) and Q*Q==Q and Q*C[4]==s.zeros(100,35)
    print('PASS intrinsic normal left inverse and rank-65 constraint projector',flush=True)
    # Whole-line compatible source projection, arbitrary ambient source refused if not in image.
    for v in [(1,s.I,0,0,2*s.I),(2+s.I,3*s.I,0,0,-s.I)]:
        c=sum((v[i]*C[i] for i in I),s.zeros(100,35)); k=sum((v[i]*K[i] for i in I),s.zeros(35,100)); q=sum(eta[i]*v[i]**2 for i in I)
        p=(c*k/q).applyfunc(s.cancel)
        assert (p*p-p).applyfunc(s.cancel)==s.zeros(100)
        assert (p*c-c).applyfunc(s.cancel)==s.zeros(100,35)
        assert (k*p-k).applyfunc(s.cancel)==s.zeros(35,100)
        bad=next(s.eye(100)[:,j] for j in range(100) if p[:,j]!=s.eye(100)[:,j]); assert (p*bad-bad).applyfunc(s.cancel)!=s.zeros(100,1)
        print('PASS compatible projector and incompatible source',v,flush=True)
    print('PASS BR219',s.__version__,flush=True)
if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier
    _,_,X,G,_,_,_,A,_,_,_,_=carrier()
    run(X,G,A)
