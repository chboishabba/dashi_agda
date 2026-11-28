import sympy as s
from itertools import combinations

def symbols(X,G):
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
    return C,K

def run(X,G):
    C,K=symbols(X,G); I=s.eye(35); J=s.eye(100); n=C[4]; L=K[4]
    assert L*n==I
    for sig in (-1,1):
        # rational complex damped frequency with nonzero normal root
        t=1+sig*s.I; k=2; b=t*C[0]+s.I*k*C[1]; a=t*K[0]+s.I*k*K[1]; lam2=t*t+k*k
        assert (a*b+lam2*I).applyfunc(s.expand)==s.zeros(35)
        assert (a*n+L*b).applyfunc(s.expand)==s.zeros(35)
        # r(0)=n v+b w-f0; r'(0)=b v+n(lam² w+L f1+a f0)-f1
        T=b.row_join(n).col_join((lam2*n).row_join(b)); assert T.rank()==60
        Q=J-n*L; assert (Q*b).rank()==25
        # 10-dimensional homogeneous admissible initial jets; all residuals retained
        N=s.Matrix.hstack(*T.nullspace()); assert N.cols==10
        assert (T*N).applyfunc(s.expand)==s.zeros(200,10)
        y=s.symbols('y',real=True)
        w=s.Matrix([s.Rational((i*i+3*i)%17-8,7)*(1+y)+s.Rational(i-11,19)*y*y for i in range(35)])
        f=n*w.diff(y)+b*w
        assert (L*f.diff(y)+a*f-w.diff(y,2)+lam2*w).applyfunc(s.expand)==s.zeros(35,1)
        source=f.subs(y,0).col_join(f.diff(y).subs(y,0)-n*(L*f.diff(y).subs(y,0)+a*f.subs(y,0)))
        assert (T*w.subs(y,0).col_join(w.diff(y).subs(y,0))-source).applyfunc(s.expand)==s.zeros(200,1)
        bad=next(J[:,i] for i in range(100) if Q[:,i]!=s.zeros(100,1) and (Q*b).row_join(Q[:,i]).rank()>25)
        assert (T.row_join(bad.col_join(s.zeros(100,1)))).rank()==61
        print('sign',sig,'initial jet rank 60, homogeneous dimension 10, constraint rank 25, incompatible initial source refused',flush=True)
    print('PASS BR220',s.__version__,flush=True)
if __name__=='__main__':
    from check_hopf369_br_curvature_energy import carrier
    _,_,X,G,_,_,_,_,_,_,_,_=carrier()
    run(X,G)
