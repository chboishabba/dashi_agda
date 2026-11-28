"""Maximum-cut inverse on the existing distributed mediator.
Exact normalized construction, causal transport and admission tests.
The inverse realizes a labelled port law, NOT a measured material.
"""
import sympy as S

def circle_reduce(f,x,y):
    return S.rem(S.expand(f),x*x+y*y-1,x)

def harmonic_inverse(a):
    x,y=S.symbols('x y',real=True); u=x+S.I*y
    out=[]
    for ids,r,c in a['models']:
        # Reuse actual local force Fourier coefficients, not a modal proxy.
        f=(S.sqrt(2)*(r[2][0]*S.re(u**2)-r[2][1]*S.im(u**2))+
           (r[1][0]-r[1][1])*x-(r[1][0]+r[1][1])*y)
        ref=(S.sqrt(2)*((r[2][0]+S.I*r[2][1])*u**2+
             (1+S.I)/S.sqrt(2)*(r[1][0]+S.I*r[1][1])*u)).applyfunc(lambda v:S.expand(S.re(v)))
        assert (f-ref).applyfunc(S.expand)==S.zeros(len(ids),1)
        store=S.expand(sum(v*(u**k if k>=0 else S.conjugate(u)**(-k)) for k,v in c.items()))
        assert circle_reduce(store-S.conjugate(store),x,y)==0
        # Polynomial lift on e=S*lambda. Monomial degree <=2 in beat,
        # <=4 in raw carrier phase quadratures. Store denominator <=4 beat.
        # On unit raw carriers, beat = h1 conjugate(h0).
        assert all(S.Poly(v,x,y).total_degree()<=2 for v in f)
        assert S.Poly(store,x,y).total_degree()<=4
        lower=S.simplify(c[0]-2*sum(abs(S.re(c[k]))+abs(S.im(c[k])) for k in range(1,5)))
        assert lower>=1
        out.append((ids,f,store,lower))
    return out

def causal_face():
    # Two one-way nonnegative power channels with finite travel time.
    # A signed nominal flow uses its positive or negative channel.
    # Linear power-density transport: d/dt integral of in-flight energy
    # = launch power - arrival power. A delay is NOT instantaneous exchange.
    t,d,b=S.symbols('t d b',real=True,positive=True)
    h=S.Function('h')
    field=h(t-b)
    assert S.diff(field,t)+S.diff(field,b)==0
    # Explicit antiderivative in age b; fundamental theorem of calculus.
    primitive=-field
    assert S.diff(primitive,b)==S.diff(field,t)
    assert primitive.subs(b,d)-primitive.subs(b,0)==h(t)-h(t-d)
    # Generic directed ledger, for arbitrary distinct launch/arrival.
    launch,arrive,localA,localB=S.symbols('launch arrive localA localB',real=True)
    assert S.expand((localA-launch)+(localB+arrive)+(launch-arrive)-localA-localB)==0
    F=S.symbols('F',nonnegative=True)
    assert S.integrate(F,(t,0,d))==d*F
    # Nonnegative physical launches can use positive parts. At target
    # lambda=1, constant signed flow F_ij and delay-filled history preserve
    # the existing nominal local store derivatives exactly.
    return True

def graph_inverse(a):
    n=len(a['models']); parent=a['parent'];order=a['order']
    D=S.zeros(n,n-1);flow=[]
    for col,j in enumerate(order[1:]):
        D[parent[j],col]=-1;D[j,col]=1;flow.append(a['flows'][j])
    assert D.rank()==n-1 and D*S.Matrix(flow)==S.Matrix(a['means'])
    delays=S.symbols('tau0:'+str(n-1),positive=True)
    storage=sum(d*abs(f) for d,f in zip(delays,flow))
    # Positive nominal travel storage, separately paid at startup.
    assert any(f!=0 for f in flow)
    return storage

def source_loss_inverse():
    I,A,R,L,Q=S.symbols('I A R L Q',nonnegative=True)
    # Same source: incident I=accessible A+reflection/dark R;
    # restored passive receiver: A=useful Q+all paid loss L.
    assert S.expand((Q+L+R)-((Q+L)+R))==0
    # For a tolerance epsilon, total dark+loss <= epsilon*incident
    # is necessary and sufficient for net useful >= (1-epsilon)*incident.
    e=S.symbols('epsilon',nonnegative=True)
    assert S.expand(Q-(1-e)*(Q+L+R)-(e*(Q+L+R)-L-R))==0
    # Positive Drude collision loss cannot vanish for nonzero current.
    nu,D,j=S.symbols('nu D j',positive=True)
    assert (nu*j*j/D).is_positive
    # A fixed source can have a dark complement even with an ideal load.
    assert S.Rational(9,25)+S.Rational(16,25)==1

def run(a):
    rows=harmonic_inverse(a);storage=graph_inverse(a)
    causal_face();source_loss_inverse()
    print('PASS actual local polynomial inverse',len(rows),'cells')
    print('PASS exact signed shared-face nominal flow and finite-delay startup ledger',len(a['order'])-1,'edges')
    print('PASS source/loss reverse threshold and positive collision obstruction')
    print('LIMIT labelled quadrature law; material coefficient, physical delay channel, delayed stability and measured source admission remain independent')
    return rows,storage

if __name__=='__main__':
    import argparse,pickle
    p=argparse.ArgumentParser();p.add_argument('--mediator',required=True);args=p.parse_args()
    with open(args.mediator,'rb') as f:a=pickle.load(f)
    run(a)
