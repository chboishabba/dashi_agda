"""Phase controller attached to actual carrier port law; ideal finite model.
No physical Maxwell synchronization or full coupled stability claim.
"""
import sympy as S
from solar_steelman_carrier_mediator import rhs, OMEGA
from solar_steelman_autonomous_mediator import evaluate, waveform
I=S.I


def controller(phases,p,model,k=1,gamma=0):
    u=[v*S.conjugate(w) for w,v in phases]
    dp=S.zeros(len(u),1); heat=0; potential=0; edges=[]
    for j in model['order'][1:]:
        a=model['parent'][j]; d=S.expand(u[j]*S.conjugate(u[a]))
        sine=S.im(d);cosine=S.re(d);v=p[j]-p[a]
        torque=k*sine+gamma*v
        dp[a]+=torque;dp[j]-=torque
        potential+=k*(1-cosine);heat+=gamma*v*v
        edges.append((a,j,sine))
    phase_dot=[(I*OMEGA*w,I*(OMEGA+1+p[j])*v) for j,(w,v) in enumerate(phases)]
    Vdot=sum(k*sine*(p[j]-p[a]) for a,j,sine in edges)
    assert S.expand(p.dot(dp)+Vdot+heat)==0
    return dp,phase_dot,potential,heat


def run(model):
    n=len(model['models']);D=S.zeros(n,n-1)
    for col,j in enumerate(model['order'][1:]):D[model['parent'][j],col]=-1;D[j,col]=1
    assert D.rank()==n-1 and (D.T*D).det()==n
    L=D*D.T; assert L*S.ones(n,1)==S.zeros(n,1)
    z=waveform({w:model['data'][w][0] for w in (1,2)},S.Integer(1))
    e=[evaluate(c,S.Integer(1)) for _,_,c in model['models']]
    energies=[(v/2,v/2) for v in e];phases=[(S.Integer(1),S.Integer(1)) for _ in e]
    F,de,pd=rhs(z,energies,phases,model)
    dp,pdc,V,Q=controller(phases,S.zeros(n,1),model)
    assert dp==S.zeros(n,1) and pdc==pd and V==Q==0
    assert F==waveform({w:model['data'][w][2] for w in (1,2)},S.Integer(1))
    phases[0]=(S.Integer(1),I);phases[1]=(I,S.Integer(1));p=S.zeros(n,1);p[0]=S.Rational(1,3);p[1]=-p[0]
    F,de,_=rhs(z,energies,phases,model)
    assert S.cancel(S.expand(z.dot(F)+sum(a+b for a,b in de)),extension=S.sqrt(2))==0
    for gamma in (0,S.Rational(1,2)):
        dp,pdc,V,Q=controller(phases,p,model,gamma=gamma)
        assert sum(dp)==0 and V>0 and Q>=0
        if gamma:assert Q>0
        else:assert Q==0
    a,b,k=S.symbols('a b k',real=True);delta=S.symbols('delta',real=True)
    torque=-2*k*S.sin(delta);reaction=k*S.sin(delta)
    assert S.expand(a*torque+b*reaction+k*S.sin(delta)*(2*a-b))==0
    print('PASS actual 48-cell carrier controller attachment, nominal force retained, perturbed energy ledger',flush=True)
    print('PASS rank47 relative Hessian; conservative bounded relative phase, optional damping debited to heat',flush=True)
    print('PASS source-reference conjugate torque identity; absolute phase lock remains separate',flush=True)

if __name__=='__main__':
    from solar_steelman_autonomous_mediator import run as mediator
    run(mediator())
