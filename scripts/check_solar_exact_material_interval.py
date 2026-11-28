"""Exact enclosure vs independent high-precision original material equations."""
from fractions import Fraction as F
import numpy as np
import mpmath as mp
from solar_event_rounding import q
from solar_material_interval import exact_material_prefix,exp_scalar
from solar_population_event import MASS,CHARGE
from solar_synthetic_fixture import fixture
from solar_spherical_geometry import geometry
from solar_earth_collision_tensor import rates
from solar_exact_tail_policy import rate_bounds


def run():
    with mp.workdps(100):
        def M(x):
            x=q(x);return mp.mpf(x.numerator)/x.denominator
        def inside(v,b):
            assert M(F(b[0]))<=v<=M(F(b[1])),(v,b)
        args=[F(0),F(1,2**300),F(1,10000),F(1),F(3),F(100),F(256),F(10**6)]
        for x in args:
            for complement in (False,True):
                a=exp_scalar(x,complement);v=-mp.expm1(-M(x)) if complement else mp.exp(-M(x));inside(v,a.serialize())
        mat,c,_,_=fixture();rows,neutral,D,g,axis=mat;n=len(rows);vol,_,_,_=geometry(c['radii_m'],c['angular_level'])
        # Exercise nonzero chemical and birth work without changing the original rate law.
        b=np.zeros((n,3,3));b[0,:,0]=1e5
        kin=dict(c['kinetics'],formation_J_per_particle=[1e-19,2e-19,3e-19],birth_velocity_m_s=b,chemical_input_efficiency=.8,chemical_recovery_efficiency=.5);c=dict(c,kinetics=kin)
        o=exact_material_prefix(mat,c,vol);assert not o['exact_charge_neutral'] # exact binary D conversion, not repaired
        pop=[[M(D[i,j])*M(MASS[j])/M(CHARGE[j])**2 for j in range(3)] for i in range(n)]
        pool=[[M(v) for v in row] for row in kin['initial_neutral_m3']];theta=[mp.mpf(0)]*n
        h=M(float(c['period_s'])/len(c['incident_sqrt_W']));a,k,g,Q=[list(map(M,kin[key])) for key in ('recombination_m3_s','ionization_s_inv','heater_ionization_per_J','activation_temperature_K')]
        V=list(map(M,vol));C=list(map(M,c['heat_capacity_J_K']));cool=list(map(M,c['cooling_W_K']));chem=list(map(M,kin['formation_J_per_particle']));paid=mp.mpf(0);birth_work=mp.mpf(0);checks=0
        powers=list(c['heating_W'])*c['max_cycles']+[np.zeros(n)]*c['restoration_steps']
        for step,p in zip(o['history'],powers):
            for i in range(n):
                P=M(p[i]);T=M(rows[i]['te'])+theta[i]
                r=[pop[i][j+1]*(-mp.expm1(-h*a[j]*pop[i][0])) for j in range(2)]
                avail=[pool[i][j]+r[j] for j in range(2)]
                created=[avail[j]*(-mp.expm1(-h*(k[j]*mp.exp(-Q[j]/T)+g[j]*P))) for j in range(2)]
                rr=[sum(r),*r];aa=[sum(created),*created]
                for z,key in ((pop[i],'old'),(rr,'removed'),(aa,'created')):
                    for v,interval in zip(z,step['events'][i][key]):inside(v,interval);checks+=1
                pop[i]=[pop[i][j]-rr[j]+aa[j] for j in range(3)];pool[i]=[avail[j]-created[j] for j in range(2)]
                bw=sum(V[i]*M(MASS[j])*aa[j]*sum(M(v)**2 for v in b[i,j])/2 for j in range(3));birth_work+=bw
                formed=sum(V[i]*aa[j]*chem[j] for j in range(3));removed=sum(V[i]*rr[j]*chem[j] for j in range(3))
                paid+=(bw+formed)/M(kin['chemical_input_efficiency'])-M(kin['chemical_recovery_efficiency'])*removed+h*P/M(c['heater_efficiency'])
                mid=mp.exp(-h*cool[i]/(2*C[i]))*theta[i]-mp.expm1(-h*cool[i]/(2*C[i]))*P/cool[i]
                theta[i]=mp.exp(-h*cool[i]/C[i])*theta[i]-mp.expm1(-h*cool[i]/C[i])*P/cool[i]
                for z,key in ((pop[i],'population'),(pool[i],'pool')):
                    for v,interval in zip(z,step[key][i]):inside(v,interval);checks+=1
                inside(mid,step['mid_temperature'][i]);inside(theta[i],step['temperature'][i]);checks+=2
        inside(paid,o['paid_J']);inside(birth_work,o['birth_work_J']);checks+=2
        lo,hi=rate_bounds(rows[0],neutral[0],20.)
        for T in np.linspace(1000,1020,21):
            r=rates([dict(te=T,ti=1000.)],neutral[:1])[0]
            assert all(float(x)<=v<=float(y) for x,v,y in zip(lo,r,hi))
        print(dict(status='EXACT_MATERIAL_INTERVAL_PASS',exp_cases=16,component_checks=checks,collision_samples=21,
            exact_charge_gap=float(F(o['exact_initial_charge_gap'][0])),paid_interval_J=[float(F(x)) for x in o['paid_J']],physical_admission=False))
if __name__=='__main__':run()
