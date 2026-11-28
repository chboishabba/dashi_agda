"""Scoped exact actuator lift of the four-phase reciprocal owner.
Frozen displacement switching; finite-inertia midpoint servo, shared bus.
Not an HF constitutive law or physical hardware identification.
"""
import sympy as S
from solar_reciprocal_periodic_switch import B,C,cycle,passive_optimum
from solar_reciprocal_continuous_inverse import stable_power,recovery_buffer
from check_v2_pulse_nonlinear_recovery import nonlinear_identity


def actuator_lift(r,schedule,m,c,tau,eta):
    m,c,tau,eta=map(S.Rational,(m,c,tau,eta))
    assert m>0 and c>0 and tau>0 and 0<=eta<=1
    dt=tau/2; work=[]; heat=0; force=[]
    for k,x in enumerate(r['states'][1:]):
        q=x[:3,:]; w=[0,0]; switch=0
        for bond,a,b in zip((B,C),schedule[k],schedule[(k+1)%4]):
            e=(bond.T*q)[0]; d=b-a; v=2*d/tau
            for j,(p0,p1,z0,z1) in enumerate(((0,v,a,(a+b)/2),(v,0,(a+b)/2,b))):
                vm=(p0+p1)/2; assert z1-z0==dt*vm
                u=m*(p1-p0)/dt+c*vm+e**2/2
                W=dt*u*vm; H=dt*c*vm**2
                assert W==m*(p1**2-p0**2)/2+e**2*(z1-z0)/2+H
                w[j]+=W; heat+=H; force.append(abs(u))
            switch+=e**2*d/2
        assert switch==r['mod'][k]
        work.extend(w)
    assert sum(work)==sum(r['mod'])+heat
    buffer=recovery_buffer(work,eta)
    if not buffer['restored']:return dict(restored=False,shortfall=buffer['shortfall'])
    conversion=(1-eta)*sum(max(0,-w) for w in work)
    output=r['receiver']+buffer['export']
    assert r['natural']==output+r['loss']+heat+conversion
    return dict(restored=True,output=output,heat=heat,conversion=conversion,
                buffer=buffer,peak_force=max(force),work=work)


def comparator():
    l=S.symbols('l',positive=True);Z=B*B.T+C*C.T+S.I*S.diag(1+l,1,1)
    q=(Z.inv()*S.Matrix([0,0,1]))[0]
    W=S.simplify(4*l*q*S.conjugate(q));assert W==4*l/(9*l*l+24*l+20)
    opt=2*S.sqrt(5)/3;cap=S.simplify(W.subs(l,opt))
    assert S.simplify(W.subs(l,1))==passive_optimum()
    assert S.simplify(cap-W-4*(3*l-2*S.sqrt(5))**2/((24+12*S.sqrt(5))*(9*l*l+24*l+20)))==0
    return cap


def run():
    assert nonlinear_identity()['residual']=='0'
    a,b=S.Rational(1,100),S.Rational(99,100);schedule=[(a,b)]*3+[(b,a)]
    r=cycle(schedule);assert stable_power(r['monodromy'])['certified']
    p=comparator()
    # Switch time is a separate frozen-displacement model clock; no power comparison.
    z=actuator_lift(r,schedule,S.Rational(1,10000),S.Rational(1,1000),1,S.Rational(3,10))
    assert z['restored'] and z['output']>p
    print('PASS', {k:float(z[k]) for k in ('output','heat','conversion','peak_force')}, 'passive_load_opt',float(p),'margin',float(z['output']-p),'buffer_capacity',float(z['buffer']['capacity']))
    # Force feedback cancels known frozen extension; tracking-error midpoint dynamics.
    m=S.Rational(1,10000);c=S.Rational(1,1000);K=S.Rational(1,100);dt=S.Rational(1,2)
    A=S.Matrix([[0,1],[-K/m,-c/m]]);I=S.eye(2);T=(I-dt*A/2).inv()*(I+dt*A/2)
    G=S.diag(K,m);R=G-T.T*G*T
    assert R.det()==0 and R.trace()>0
    O=S.Matrix.vstack(S.Matrix([[0,1]])*(I-dt*A/2).inv(),S.Matrix([[0,1]])*(I-dt*A/2).inv()*T)
    assert O.det()!=0
    print('PASS exact actuator tracking contraction over two steps; not full hybrid stability')
    bad=actuator_lift(r,schedule,S.Rational(1,10000),1,1,S.Rational(3,10));assert not bad['restored']
    off=cycle(schedule,[S.zeros(3,1)]*4);assert off['receiver']==0
    print('PASS excess damping and source-off negative controls')
if __name__=='__main__':run()
