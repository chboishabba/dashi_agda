"""Symbolic event and native indexed Cayley coefficient parity."""
import numpy as np
import sympy as S
from solar_quadratic_jet import amplitude2,event_state2,reaction_u2,work2,squared_return2
from solar_physical_cone import timed_step


def run():
    s=S.symbols('s',positive=True); u=S.symbols('u',real=True)
    cases=[((4,1,2),(2,1,1),(1,2,0)),((0,4,1),(0,2,1),(0,3,2)),
           ((0,0,4),(0,0,2),(0,0,1)),((0,0,0),(0,0,0),(0,0,9)),
           ((4,2,3),(0,2,1),(0,0,3)),((4,2,3),(0,0,2),(0,0,1)),
           ((0,4,2),(0,1,0),(4,0,1)),((0,0,4),(0,0,2),(3,1,0)),
           ((0,4,2),(0,0,1),(0,0,2))]
    def poly(t): return sum(c*s**(2*i) for i,c in enumerate(t))
    def jet(z): return S.expand(S.series(z,s,0,3).removeO())
    for ns,fs,aas in cases:
        N,F,A=map(poly,(ns,fs,aas)); M=F+A; v=2+3*s+5*s*s; b=-2
        old=S.sqrt(N)*v; new=(F*v+A*b)/S.sqrt(M); j=jet(old)
        zs=[np.full((3,3),float(j.coeff(s,i))) for i in range(3)]
        n=np.tile(np.array(ns,float)[:,None],(1,3)); f=np.tile(np.array(fs,float)[:,None],(1,3)); a=np.tile(np.array(aas,float)[:,None],(1,3));r=n-f
        z2,k2=event_state2(*zs,n[0],r[0],a[0],n[1],r[1],a[1],n[2],r[2],a[2],np.full((3,3),b),np.ones(3),return_kinetic=True)
        assert np.allclose(z2,float(jet(new).coeff(s,2)),rtol=1e-12,atol=1e-12)
        assert np.allclose(amplitude2(*(n-r+a)),float(jet(S.sqrt(M)).coeff(s,2)))
        assert S.cancel((new**2-old**2)/2-A*b*b/2+(N-F)*v*v/2+F*A/M*(v-b)**2/2)==0
        assert np.allclose(k2,[9*float(jet(expr).coeff(s,2)) for expr in (A*b*b/2,(N-F)*v*v/2,F*A/M*(v-b)**2/2)],rtol=1e-12,atol=1e-12)
    # Independent symbolic reaction coefficient, two charge-neutral channels.
    n=np.array([5.,3.,2.]); nu=np.array([.3,.2,.1]); n2=np.array([.04,.03,.01]); pool=np.array([2.,4.]); pu=np.array([.1,.2]); p2=np.array([.03,.04])
    q=dict(recombination_m3_s=[.2,.1],ionization_s_inv=[.3,.4],heater_ionization_per_J=[.2,.1],activation_temperature_K=[3.,5.])
    T=9.;Tu=.5; p=.6; dp=.2; h=.25
    r2,a2,pp2=reaction_u2(n,pool,T,p,h,q,nu,pu,Tu,dp,n2,p2)
    R=[];A=[];B=[]
    for j in range(2):
        rat=lambda z:S.Rational(str(float(z)))
        N=[rat(n[k])+u*rat(nu[k])+u*u*rat(n2[k]) for k in (0,j+1)]
        r=N[1]*(1-S.exp(-rat(h*q['recombination_m3_s'][j])*N[0])); av=rat(pool[j])+u*rat(pu[j])+u*u*rat(p2[j])+r
        rate=rat(q['ionization_s_inv'][j])*S.exp(-rat(q['activation_temperature_K'][j])/(rat(T)+u*rat(Tu)))+rat(q['heater_ionization_per_J'][j])*(rat(p)+u*rat(dp))
        a=av*(1-S.exp(-rat(h)*rate))
        for target,expr in ((R,r),(A,a),(B,av-a)): target.append(float(S.diff(expr,u,2).subs(u,0)/2))
    assert np.allclose(r2,np.r_[sum(R),R]);assert np.allclose(a2,np.r_[sum(A),A]);assert np.allclose(pp2,B)
    mesh=dict(positions_m=[[0,0,0],[1,0,0],[2,0,0]],coordinate_site=[0,1,2],faces=[dict(id='a',source=0,target=1,normal=[1,0,0],area_m2=1),dict(id='b',source=1,target=2,normal=[1,0,0],area_m2=1)],front_speed_m_s=100.)
    H=np.diag([-.25,0.,0.]);P=H.copy();P[1,1]=-.5; A1=np.zeros((3,3));A1[0,1]=-1.;A1[1,0]=1.;A2=np.zeros((3,3));A2[0,1]=.3;A2[1,0]=-.3;A2[1,2]=-2.;A2[2,1]=2.
    L=np.array([.25,0,0]);Lu=np.array([.1,0,0]);A2[0,0]-=.1
    z=np.array([1.,0,0]); f=np.zeros(3); h=.25; pairs=((0,1),(1,2))
    x=z.copy(); x1=f.copy(); x2=f.copy(); w0=w1=w2=0.
    for _ in range(2):
        x,rec=timed_step(x,H,f,h,mesh,retain_local_midpoint=True,jvp=(x1,A1,f),atlas_pairs=pairs,right_limit=P,jet2=(x2,A2,f))
        assert rec['coefficient2_balance_abs_J']<1e-12
        x1=np.asarray(rec['state_jvp']);x2=np.asarray(rec['state_coefficient2'])
        m=np.asarray(rec['local_midpoint']);m1=np.asarray(rec['local_midpoint_jvp']);m2=np.asarray(rec['local_midpoint_coefficient2'])
        w0+=h*float(m@(L*m));w1+=2*h*float(m@(L*m1));w2+=h*work2(m,m1,m2,L,Lu)
    # Second-only dormant exchange from an inhabited primal coordinate.
    zz=np.array([0.,1.,0.]); zz0,rec=timed_step(zz,P,f,h,mesh,jvp=(f,np.zeros_like(P),f),atlas_pairs=pairs,right_limit=P,jet2=(f,A2,f))
    assert rec['state_coefficient2'][2]!=0 and rec['arrival_s'][2] is None and rec['directional_arrival_s'][2] is None
    assert rec['coefficient2_arrival_s'][2] is not None
    errs=[]
    for eps in (.01,.001,.0001):
        y=z.copy(); w=0.
        for _ in range(2):
            y,rec=timed_step(y,P+eps*A1+eps*eps*A2,f,h,mesh,retain_local_midpoint=True,atlas_pairs=pairs)
            m=np.asarray(rec['local_midpoint']);w+=h*float(m@((L+eps*eps*Lu)*m))
        errs.append([float(np.linalg.norm((y-x-eps*x1)/eps**2-x2)),float(abs((w-w0-eps*w1)/eps**2-w2))])
    assert max(errs[-1])<.001
    # Same original-coordinate squared return, not norm differentiation.
    assert np.isclose(squared_return2([x],[z],[x1],[x2])[0],np.dot(x1,x1)+2*np.dot(x-z,x2))
    print(dict(status='QUADRATIC_JET_PASS',event_cases=len(cases),errors=errs,work2=w2,state2=x2.tolist(),physical_admission=False))

if __name__=='__main__':run()
