"""Exact four-phase reciprocal chain; switching work at fixed displacement.
Reconstruction of documented M1, not native package or physical actuator.
"""
import sympy as S
from itertools import product

B=S.Matrix([1,-1,0]); C=S.Matrix([0,1,-1]); I=S.eye(3)
D=S.diag(2,1,1); h=S.Integer(2)
FORCES=[S.Matrix([0,0,f]) for f in (1,0,-1,0)]

def stiffness(a,b):
    a,b=map(S.Rational,(a,b))
    if not (0<=a<=1 and 0<=b<=1):raise ValueError('coupling range')
    return I+a*B*B.T+b*C*C.T

def maps(K):
    A=S.zeros(6); A[:3,3:]=I; A[3:,:3]=-K; A[3:,3:]=-D
    L=(S.eye(6)-h*A/2).inv()
    F=S.zeros(6,3);F[3:,:]=I
    return L*(S.eye(6)+h*A/2),h*L*F

def cycle(schedule,forces=FORCES):
    if len(schedule)!=4 or len(forces)!=4:raise ValueError('four phases')
    Ks=[stiffness(*p) for p in schedule];steps=[maps(K) for K in Ks]
    M=S.eye(6);b=S.zeros(6,1)
    for (T,F),f in zip(steps,forces):M=T*M;b=T*b+F*f
    L=S.eye(6)-M
    if L.det()==0:return dict(status='UNRESOLVED_SINGULAR')
    x=L.inv()*b;initial=x;states=[x];vel=[];mod=[];N=Y=loss=0
    for k,((T,F),f,K) in enumerate(zip(steps,forces,Ks)):
        y=T*x+F*f;q=y[:3,:];v=(x[3:,:]+y[3:,:])/2;vel.append(v)
        W=h*(v.T*f)[0];U=h*v[0]**2;H=h*(v.T*v)[0]
        G=S.diag(K,I);assert ((y.T*G*y-x.T*G*x)[0]/2)==W-U-H
        m=(q.T*(Ks[(k+1)%4]-K)*q)[0]/2;mod.append(m)
        N+=W;Y+=U;loss+=H;states.append(y);x=y
    assert x==initial and N+sum(mod)==Y+loss
    gross=sum(max(0,m) for m in mod);recover=sum(max(0,-m) for m in mod)
    return dict(status='PERIODIC',states=states,vel=vel,mod=mod,natural=N,receiver=Y,loss=loss,
                ideal=Y-sum(mod),gross_net=Y-gross,recover=recover,buy=gross,monodromy=M)

def passive_optimum():
    a,b=S.symbols('a b',real=True)
    Z=a*B*B.T+b*C*C.T+S.I*D
    den=16*a*a*b*b+9*a*a+8*a*b+16*b*b+4
    q=(Z.inv()*S.Matrix([0,0,1]))[0]
    assert S.simplify(S.expand_complex(q*S.conjugate(q))-a*a*b*b/den)==0
    # Divide denominator by a²b²: every nonconstant term decreases as
    # positive a,b increase. Boundary a*b=0 gives zero transfer.
    return S.Rational(4,53)

def reverse_schedule(states,forces=FORCES):
    """Invert midpoint forces to signed bond coefficients; free bonds explicit."""
    if len(states)!=5 or states[0]!=states[-1]:raise ValueError('return')
    out=[]
    for x,y,f in zip(states,states[1:],forces):
        q=(x[:3,:]+y[:3,:])/2;v=(x[3:,:]+y[3:,:])/2
        if y[:3,:]-x[:3,:]!=h*v:return None
        rhs=f-D*v-q-(y[3:,:]-x[3:,:])/h
        if sum(rhs)!=0:return None
        vals=[]
        for bond,force in [(B,rhs[0]),(C,-rhs[2])]:
            z=(bond.T*q)[0]
            if z==0:
                if force!=0:return None
                vals.append(None)
            else:
                a=force/z
                if not 0<=a<=1:return None
                vals.append(a)
        out.append(tuple(vals))
    return out

def velocity_budget(receipt):
    """All restored four-phase schedules: internal bond forces cancel.
    Fundamental midpoint velocities a,b are real signed quadratures.
    The source/loss ceiling is independent of selected coupling schedule.
    """
    v=receipt['vel'];a,b=v[0],v[1];u=S.Matrix([2,1,1]);c=S.Matrix([0,0,S.Rational(1,2)])
    assert v[2]==-a and v[3]==-b
    assert (u.T*a)[0]==1 and (u.T*b)[0]==0
    center=c+u*(1-(u.T*c)[0])/(u.T*u)[0]
    cap=S.Rational(5,6);gap=4*((a-center).dot(a-center)+b.dot(b))
    assert cap-receipt['ideal']==gap
    return dict(cap=cap,center=center,gap=gap)

def binary_global():
    """All 256 binary four-phase schedules, exact scoped global comparison.
    Not a relaxation or proof of optimality for intermediate couplings.
    """
    rows=[];P=passive_optimum()
    for schedule in product(list(product((0,1),repeat=2)),repeat=4):
        a=cycle(schedule);assert a['status']=='PERIODIC'
        velocity_budget(a)
        inv=reverse_schedule(a['states']);assert inv is not None
        assert all(v is None or v==s for pair,sp in zip(inv,schedule) for v,s in zip(pair,sp))
        rows.append((a['gross_net'],a['ideal'],schedule,a['receiver'],a['buy'],a['recover']))
    gross=max(rows,key=lambda x:x[0]);ideal=max(rows,key=lambda x:x[1])
    assert gross[0]==P and len(rows)==256
    threshold=(P-ideal[0])/ideal[5];assert 0<threshold<1
    # Across all binary schedules, reverse the least recovery efficiency for
    # strict gain over passive. With positive overhead or desired gain the
    # numerator increases; zero recovery cannot beat passive on this domain.
    eligible=[((P-x[0])/x[5],x) for x in rows if x[5]>0 and x[1]>P]
    best=min(eligible,key=lambda x:x[0]);assert 0<best[0]<=threshold
    return dict(count=len(rows),gross=gross,ideal=ideal,ideal_optimum_recovery=threshold,
                least_recovery=best[0],least_recovery_schedule=best[1][2],least_recovery_row=best[1],
                ideal_beats=sum(1 for x in rows if x[1]>P))

def run():
    P=passive_optimum();p=cycle([(1,1)]*4);assert p['receiver']==P==p['gross_net']
    # The fixed-source cap follows directly by square completion at each step.
    cap=sum(h*f[2]**2/4 for f in FORCES);assert cap==1
    # A reverse target at the passive optimum reopens exactly. A prescribed
    # nonphysical trajectory is refused instead of choosing a coupling.
    r=reverse_schedule(p['states']);assert r is not None and all(v in (1,None) for pair in r for v in pair)
    bad=[x.copy() for x in p['states']];bad[1][0]+=1;assert reverse_schedule(bad) is None
    # Scoped switched candidates, not a continuous-domain optimization.
    candidates=[[(1,1),(0,1),(1,1),(0,1)],[(1,1),(1,0),(1,1),(1,0)],[(1,0),(0,1),(1,0),(0,1)],[(1,1),(1,0),(0,1),(1,1)]]
    for sched in candidates:
        a=cycle(sched);assert a['status']=='PERIODIC';assert a['gross_net']<=a['ideal']<=cap
        inv=reverse_schedule(a['states']);assert inv is not None
        assert all(v is None or v==s for pair,sp in zip(inv,sched) for v,s in zip(pair,sp))
        print('candidate',sched,'receiver',float(a['receiver']),'net',float(a['gross_net']),'ideal',float(a['ideal']))
    off=cycle(candidates[0],[S.zeros(3,1)]*4);assert off['receiver']==off['gross_net']==0
    print('PASS passive',P,'all_schedule_cap',cap,'four candidate inverses and source-off')
    print('BINARY_GLOBAL',binary_global())
if __name__=='__main__':run()
