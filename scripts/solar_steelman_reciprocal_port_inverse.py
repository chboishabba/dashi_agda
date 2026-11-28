"""Minimum reciprocal extension of actual cell force to an energy port.
Constructed normalized law, not an identified material susceptibility.
"""
import sympy as S
from solar_steelman_physical_inverse import harmonic_inverse, circle_reduce

def construct(a):
    x,y=S.symbols('x y',real=True);u=x+S.I*y
    rows=harmonic_inverse(a);out=[]
    for ids,F,store,lower in rows:
        # In energy-normalized auxiliary amplitude h, e=h²/2.
        # The minimal one-port skew extension couples material effort z
        # and auxiliary effort h. F_actual = (h²/2S) F.
        h=S.symbols('h',real=True)
        z=S.Matrix(S.symbols('z:'+str(len(ids)),real=True))
        K=h*F/(2*store)
        # Material kinetic metric is handled by the original H/alpha;
        # these are effort/flow ports, not Euclidean current derivatives.
        material=K*h;aux=-(K.T*z)[0]
        assert S.cancel(z.dot(material)+h*aux)==0
        assert all(S.cancel(v)==0 for v in material-h*h*F/(2*store))
        # Nominal local current and auxiliary energy exchange.
        zz={w:tuple(v[ids,:] for v in a['data'][w][0]) for w in (1,2)}
        Z=S.sqrt(2)*(zz[2][0]*(x*x-y*y)-zz[2][1]*2*x*y)+(zz[1][0]-zz[1][1])*x-(zz[1][0]+zz[1][1])*y
        dstore=-y*S.diff(store,x)+x*S.diff(store,y)
        mean=a['means'][len(out)]
        assert circle_reduce(dstore+Z.dot(F)-mean,x,y)==0
        out.append(dict(ids=ids,force=F,store=store,lower=lower,port=K))
    assert sum(a['means'])==0
    print('PASS actual reciprocal one-port local extension',len(out),'cells',flush=True)
    print('LIMIT variable skew port law is not automatically Poisson, Maxwell susceptibility or measured material')
    return out

def fixture():
    h,s,z,f=S.symbols('h s z f',real=True,nonzero=True)
    K=h*f/(2*s)
    assert S.cancel(z*K*h+h*(-K*z))==0
    # Exact one auxiliary effort is sufficient; no auxiliary effort
    # cannot carry nonzero local material work under skew self-coupling.
    print('PASS reciprocal effort-flow identity')

if __name__=='__main__':
    import argparse,pickle
    p=argparse.ArgumentParser();p.add_argument('--mediator');x=p.parse_args()
    fixture()
    if x.mediator:
        with open(x.mediator,'rb') as f:a=pickle.load(f)
        construct(a)
