"""Original FV source versus common scalar Bessel transform; dimensionless radius.
No source replacement or receiver calibration. Import existing producer.
"""
import numpy as np
from scipy.special import spherical_jn, roots_legendre
from scipy.integrate import quad
from ksw668_f8_fv_source_flux import exact_cell_averages,compact_bump

def run():
    k=np.array([.1,.25,.5,1.,2.,4.,8.,16.,32.])
    x,w=roots_legendre(512); u=(x+1)/2;w=w/2
    B=(w*u*u*np.exp(1-1/(1-u*u)))@np.sinc(u[:,None]*k[None,:]/np.pi)
    target=np.array([.4*k**4,-60/7*k*k,np.full_like(k,27)])*B
    for dr in (.008,.006,.004,.003,.002):
        h=dr/.04; n=int(np.ceil(3.01/dr)); r=np.arange(n)*h
        src=exact_cell_averages(.04,r*.04,dr)
        for q,l in enumerate((0,2,4)):
            d=3+2*l; a=np.maximum(0,r-h/2);b=r+h/2;mass=(b**d-a**d)/d
            active=src[q]!=0; rr=r[active]; aa=a[active];bb=b[active];mm=mass[active];ss=src[q,active]
            def phi(z):
                p=np.ones_like(z); np.divide(spherical_jn(l,z)*[1,15,945][q],z**l,out=p,where=z!=0);return p
            nodal=(mm*ss)@phi(rr[:,None]*k)
            # Integrate piecewise-constant reconstruction against Bessel kernel,
            # rather than replacing the source by nodal samples.
            z=aa[:,None]+(bb-aa)[:,None]*u
            integ=np.einsum('ij,ijk->ik',(bb-aa)[:,None]*w*z**(d-1),phi(z[:,:,None]*k))
            pc=ss@integ
            # Exact source's low-frequency monopole quadratic leakage.
            m1=np.dot(mm*ss,rr**2); m1pc=np.dot(ss,(bb**(d+2)-aa**(d+2))/(d+2))
            print(dr,l,'M1 nodal/cell',m1,m1pc,'k=.1 exact/nodal/cell',target[q,0],nodal[0],pc[0],'relative L2 nodal/cell',np.linalg.norm(nodal-target[q])/np.linalg.norm(target[q]),np.linalg.norm(pc-target[q])/np.linalg.norm(target[q]),flush=True)
    print('Bessel comparison complete: 135 frequencies per route; not a receiver error estimate')
if __name__=='__main__':run()
