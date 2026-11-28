"""BR305 sourced harmonic subsidiary identity on FLRW symmetry reduction.
Independent normal-time check in dimensions 4 and 5; not full PDE stability.
"""
import sympy as s

def run(m):
    t=s.symbols('t',real=True);a=s.Function('a',positive=True)(t);rho=s.Function('rho')(t);p=s.Function('p')(t);k=s.symbols('kappa');H=s.diff(a,t)/a
    D=lambda x:s.diff(x,t)
    # A covariant diagonal tensor with components X00 and Xii/a^2.
    trace=lambda X:-X[0]+m*X[1]
    trrev=lambda X:(X[0]+trace(X)/2,X[1]-trace(X)/2)
    divergence=lambda X:-D(X[0])-m*H*(X[0]+X[1])
    add=lambda X,Y:tuple(x+y for x,y in zip(X,Y))
    scale=lambda c,X:tuple(c*x for x in X)
    g=(-1,1);T=(rho,p);R=(-m*D(D(a))/a,D(D(a))/a+(m-1)*H**2)
    Lam=s.symbols('Lambda');C=-m*H;B=(D(C),-H*C)
    S=add(T,scale(-trace(T)/(m-1),g))
    E=add(add(add(R,scale(-1,B)),scale(-k,S)),scale(-2*Lam/(m-1),g))
    physical=add(add(trrev(R),scale(Lam,g)),scale(-k,T))
    assert all(s.simplify(x-y)==0 for x,y in zip(physical,add(trrev(E),trrev(B))))
    assert s.simplify(divergence(trrev(R)))==0
    # Direct second covector derivative, not inferred from divergence identity.
    wave=-D(D(C))-m*H*D(C)+m*H**2*C
    ric=m*D(D(a))/a*C
    assert s.simplify(2*divergence(trrev(B))-wave-ric)==0
    assert s.simplify(wave+ric+2*k*divergence(T)+2*divergence(trrev(E)))==0
    assert s.simplify(divergence(T))!=0
    print('BR305 dimension',m+1,'exact trace reversal, contracted Bianchi and sourced subsidiary normal component PASS',flush=True)
if __name__=='__main__':
    for m in (3,4):run(m)
