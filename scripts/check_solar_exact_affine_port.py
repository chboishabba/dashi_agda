"""Exact affine port residual against independently solved rational scalar stage."""
from fractions import Fraction as F
import numpy as np
from solar_physical_cone import timed_step

def run():
    m=dict(positions_m=[[0,0,0]],coordinate_site=[0],faces=[]);errors=[]
    for p,l,inc,h,x in [(0.1,.2,.3,.4,.5),(.33,1e-18,.7,1.,.1),(.7,.01,-.23,.3,.5)]:
        B=np.zeros((1,1));L=np.array([[l]]);S=np.array([[p*p]]);H=B-L-S
        y,r=timed_step(np.array([x]),H,np.array([2*inc*p]),h,m,dict(load=L,source=S),np.array([p]),inc,True,True,exact_port_base=B)
        a=-F(l)-F(p)**2;b=2*F(inc)*F(p)
        Y=((1+F(h)*a/2)*F(x)+F(h)*b)/(1-F(h)*a/2)
        exact=abs(F(float(y[0]))-F(x)-F(h)*(a*(F(x)+F(float(y[0])))/2+b))
        err=F(r['exact_binary_stage_error']);assert err==exact and abs(F(float(y[0]))-Y)<=err
        mid=F(r['exact_binary_midpoint_error'][0]);assert abs(F(r['local_midpoint'][0])-(F(x)+Y)/2)<=mid
        errors.append(float(err))
    print(dict(status='EXACT_AFFINE_PORT_PASS',cases=3,residuals=errors))
if __name__=='__main__':run()
