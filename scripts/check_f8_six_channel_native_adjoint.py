"""D3 reduced actual weighted4 six-channel stage/RK/receiver parity.
Not full physical receiver production or uniform convergence.
"""
import numpy as np
from scipy.optimize import brentq
from ksw668_f8_tt_multipole import F
from ksw668_f8_fv_source_flux import exact_cell_averages
from ksw668_f8_signed_route_stage import rhs,rhs_transpose,step,reverse_step,receiver_defect_ledger
from warp_native_geometric_receiver import receiver_bank
from warp_israel_affine import radial_source_at_receiver,offsets,forced_identity

def run():
    rng=np.random.default_rng(1547)
    dr,dy,dt,eps=.008,.012,.0003,.04
    ny,nr=5,13
    src=exact_cell_averages(eps,np.arange(nr)*dr,dr)
    cp=np.zeros_like(src);cm=cp.copy()
    j=np.arange(1,nr)
    for q,d in enumerate((3,7,11)):
        den=(j+.5)**d-(j-.5)**d
        cp[q,1:]=d*(j+.5)**(d-1)/den
        cm[q,1:]=d*(j-.5)**(d-1)/den
    def coeff(T):
        t=brentq(lambda t:F(t)-T,.5,25)
        v=-1/np.sqrt(1+t*t)
        return v,1/t,.013*np.cos(T)
    def projected():
        X=rng.normal(size=(6,3,ny,nr))*1e-4
        X[..., -1]=0
        return X
    count=dict(stage=0,rk=0,receiver=0)
    for route in ('paired','ledger'):
        for t in (1.,2.,12.):
            T0=F(t)-dt
            x,y=projected(),projected()
            def forward(x,T):return step(x,T,dt,coeff,dr,dy,src,cp,cm,route)
            for T in (T0,T0+dt/2,T0+dt):
                v,b,a=coeff(T)
                L=rhs(x,dr,dy,b,v,a,src,cp,cm,route)-rhs(np.zeros_like(x),dr,dy,b,v,a,src,cp,cm,route)
                np.testing.assert_allclose(np.vdot(L,y),np.vdot(x,rhs_transpose(y,dr,dy,b,v,route)),rtol=1e-10,atol=1e-12)
                count['stage']+=1
            L=forward(x,T0)-forward(np.zeros_like(x),T0)
            np.testing.assert_allclose(np.vdot(L,y),np.vdot(x,reverse_step(y,T0,dt,coeff,dr,dy,route)),rtol=1e-10,atol=1e-12)
            count['rk']+=1
            base=[projected()];other=[base[0]+projected()]
            defects=[]
            for n in range(2):
                T=T0+n*dt
                base.append(forward(base[-1],T))
                d=projected();defects.append(d)
                other.append(forward(other[-1],T)+d)
            errors=[y-x for x,y in zip(base,other)]
            vel=np.array([coeff(T0+i*dt/2)[0] for i in range(5)])
            rx=.025
            bank=receiver_bank(t,rx,eps,dr,dy,dt,vel,1,nr,ny)
            g=radial_source_at_receiver(src,coeff(F(t))[2],rx,eps,dr)
            values=[]
            for row in bank:
                obs=np.zeros((3,6,3,ny,nr));obs[:,:3]=row
                out=receiver_defect_ledger(obs,errors,defects,T0,dt,coeff,dr,dy,route)
                values.append(out['actual']);count['receiver']+=1
            # Same prescribed source cancels in difference; separately test actual affine identity.
            actual=np.einsum('csiqyr,siqyr->cq',bank,np.array(other)[:,:3])+offsets(g)
            e,s=forced_identity(actual,g,t)
            assert np.all(abs(e)<=1e-10*np.maximum(1.,s))
    print(count)
if __name__=='__main__':run()
