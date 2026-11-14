#!/usr/bin/env python3
"""Independent replay: TWO-MOUTH EFFECTIVE Einstein/Maxwell junction, not a renormalized 4D Dirac state.
Sources: MMP 2018/2023, Polyakov 2D anomaly, spin-c S2 Dirac spectrum.
The static fixed Casimir state and truncated modes are manually switched off outside junction.
"""
import math
from scipy.integrate import solve_ivp,quad
from scipy.optimize import brentq
from scipy.special import kv
PI=math.pi
def potential(q,r,L,levels=4,winding=40):
    return sum(-4*(abs(q)+2*n)*m/(PI*L)*sum((1 if k%2 else -1)*kv(1,k*m*L)/k for k in range(1,winding+1))
        for n in range(1,levels+1) for m in (math.sqrt(n*(n+abs(q)))/r,))
def potential_prime(q,r,L):
    h=1e-4*r
    return (potential(q,r+h/2,L)-potential(q,r-h/2,L))/h
def run(q,L=20.,extent=100.,with_profile=False):
    Q=q/2.; c=abs(q);t=-PI*c/(12*L*L)
    def V(rad):return potential(q,rad,L)
    def throat(a):return Q**2/a**2-(1+4*t-2*V(a))
    a=brentq(throat,Q*.5,Q*2,xtol=1e-12)
    def equations(x,y):
        r,v,F,logN=y;N=math.exp(logN);U=V(r);dU=potential_prime(q,r,L)
        R=1-v*v-Q**2/r**2-c/(12*PI)*F**2-4*t/N**2-2*U
        S=-F*F-F*v/r+Q**2/r**4-dU/r
        Fpp=(R-2*r*r*S)/(c/(6*PI)-2*r*r)
        rpp=r*(S-Fpp)
        return [v,rpp,Fpp,F]
    def pres(y):
        r,_,F,logN=y
        return -c*F*F/(24*PI)+2*t/math.exp(2*logN)-V(r)
    def crossing(x,y):return pres(y)
    crossing.terminal=True;crossing.direction=1
    sol=solve_ivp(equations,(0,extent),(a,0.,0.,0.),events=crossing,
        rtol=4e-9,atol=2e-10,max_step=.2,dense_output=True)
    assert sol.success and len(sol.t_events[0])==1, (q,sol.message,sol.t[-1])
    x=float(sol.t_events[0][0]);rad,v,F,logN=sol.sol(x)
    M=rad/2*(1+Q**2/rad**2-v*v)
    f=1-2*M/rad+Q**2/rad**2
    assert f>0 and v>0
    Kdifference=F-(M/rad**2-Q**2/rad**3)/math.sqrt(f)
    constraint=v*v-1+2*rad*v*F+Q**2/rad**2-2*pres(sol.sol(x))
    horizon=M+math.sqrt(max(0,M*M-Q*Q)) if M>=Q else 0
    assert rad>horizon and abs(Kdifference)<1e-8 and abs(constraint)<1e-8
    def weighted_nec(xx):
        r,v,F,logN=sol.sol(xx);N=math.exp(logN)
        Fpp=equations(xx,(r,v,F,logN))[2]
        return (c*Fpp/(12*PI)+4*t/N**2)/(4*PI*r*r*N)
    anec=2*quad(weighted_nec,0,x,epsabs=1e-7)[0]
    lighttime=2*quad(lambda xx:math.exp(-sol.sol(xx)[3]),0,x,epsabs=2e-7)[0]
    assert anec<0
    result=dict(q=q,throat_radius=a,match_x=x,match_radius=float(rad),
      mass_RN=float(M),Q=Q,Ktt_jump=float(Kdifference),
      radial_constraint=float(constraint),radial_ANEC=float(anec),
      interior_radial_lighttime=float(lighttime),external_horizon_radius=float(horizon),
      model='classical GR + fixed Polyakov state + finite KK Dirac tower, cut off at RN junction')
    if with_profile:
        result['numerical_profile']=sol
        result['lapse_scale_to_RN_clock']=math.sqrt(f)/math.exp(logN)
    return result
def main():
    values=[run(q) for q in (10,11,12,13,24)]
    for d in values:
        print('PASS q',d['q'],'R',round(d['match_radius'],6),
          'M',round(d['mass_RN'],6),'Ktt',round(d['Ktt_jump'],12),
          'ANEC',round(d['radial_ANEC'],9))
    x=next(v for v in values if v['q']==12)
    assert abs(x['match_radius']-11.683162)<0.005
    assert abs(x['mass_RN']-5.997338)<0.005
    print('PASS: P=0 two-mouth classical effective RN junction replay; quantum-state extension NOT proved')
    return values
if __name__=='__main__': main()
