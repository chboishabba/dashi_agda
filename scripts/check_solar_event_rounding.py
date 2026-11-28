"""Exact square-root brackets and original nontrivial population event rounding."""
import numpy as np
import sympy as S
from fractions import Fraction as F
from solar_population_event import event,MASS,CHARGE
from solar_event_rounding import sqrt_interval,event_rounding_receipt

def run():
    for v in (F(0),F(1),F(2),F(3,7),F(2)**-1000,F(2)**1000,F(3,5)*F(2)**-700):
        a,b=sqrt_interval(v);assert 0<=a<=b and a*a<=v<=b*b
    rng=np.random.default_rng(369);worst=0.;cases=0
    for n,r,a in (([4,3,1],[1,1,0],[2,1,1]),([0,0,0],[0,0,0],[3,2,1]),([4,3,1],[4,3,1],[0,0,0]),([4,3,1],[1,0,1],[0,0,0])):
        n,r,a=map(lambda v:np.array(v,float),(n,r,a));V=.123
        b=rng.normal(size=(3,3))*1e5;z=(np.sign(CHARGE)*np.sqrt(V*MASS*n))[:,None]*rng.normal(size=(3,3))*1e5
        out,_,_=event(z,n,r,a,b,V);rec=event_rounding_receipt(z,n,r,a,b,V,MASS,CHARGE,out)
        Q=lambda v:S.Rational(float(v))
        for j in range(3):
            N,R,A=map(Q,(n[j],r[j],a[j]));rem=N-R;new=rem+A
            coef=rem/S.sqrt(N*new) if N*new else 0
            shift=S.sign(Q(CHARGE[j]))*A*S.sqrt(Q(V)*Q(MASS[j])/new) if new else 0
            for k in range(3):
                i=j*3+k;exact=coef*Q(z[j,k])+shift*Q(b[j,k]);l,u=map(S.Rational,rec['output_intervals_exact'][i])
                assert S.sign(exact-l)>=0 and S.sign(u-exact)>=0
                assert abs(Q(out[i])-exact)<=S.Rational(rec['component_error_exact'][i])
        worst=max(worst,float(F(rec['error_l1_exact'])));cases+=1
    print(dict(status='EVENT_ROUNDING_PASS',sqrt_cases=7,event_cases=cases,components=cases*9,max_l1_radius=worst))
if __name__=='__main__':run()
