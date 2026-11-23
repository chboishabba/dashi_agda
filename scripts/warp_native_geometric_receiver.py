"""Independent receiver rows on reconstructed native FV wall jets.
Finite diagnostic reconstruction; no strong trace convergence assertion.
"""
import numpy as np

def rows(t):
    b=1/t;v=-1/np.sqrt(1+t*t);a=t**3/(1+t*t)**2;c=1-v*v
    S=np.sqrt(1+t*t)/t;J=-1/(t*np.sqrt(1+t*t))
    A,B,D,E,Y,L,X=np.eye(7)
    F=v*A+c*D
    R=-B+2*v*E+c*Y+(a-3/b)*D+L
    box=-B+2*v*E+c*Y+a*D+L
    N=v*v*B+2*v*c*E+c*c*Y-v*v*a*D
    return np.array([-b*b*(S*S*B+J*A-L)/4,
        -b*b*(S*S*B+J*A+X)/4,
        b*b*(-N/(2*c)+box/6),
        -b*b*(S*S*B+(J+2*S)*A-L)/2,F,R])

def receiver_bank(t,rx,eps,dr,dy,h,vel,nt,nr,ny):
    """Rows E4, legacy4, direct, SMS, F, R; three time slots.
    U is displacement; T derivatives use native Udot=(1+v)P/2+(1-v)M/2.
    Normal derivatives use independent one-sided polynomial traces.
    """
    if ny<3 or min(rx,eps,dr,dy,h,t)<=0:raise ValueError('jet geometry')
    ir=int(rx/dr);idx=np.arange(ir-1,ir+3)
    if idx[0]<0 or idx[-1]>=nr-1:raise ValueError('active receiver stencil')
    delta=idx-rx/dr
    V=delta[None,:]**np.arange(4)[:,None]
    rhs=np.zeros((4,3));rhs[0,0]=1;rhs[1,1]=1/dr;rhs[2,2]=2/dr**2
    w,dw,dd=np.linalg.solve(V,rhs).T
    d=np.array([-3.,4.,-1.])/(2*dy);d2=np.array([1.,-2.,1.])/dy**2
    jets=np.zeros((7,3,3,3,ny,nr))
    for q,ell in enumerate((0,2,4)):
        fac=(rx/eps)**ell
        for i,sign in enumerate((-1,0,1)):
            k=2*(nt+sign)
            for comp,coef in ((1,(1+vel[k])/2),(2,(1-vel[k])/2)):
                if sign==0:jets[0,i,comp,q,0,idx]=fac*w*coef
                jets[1,i,comp,q,0,idx]=fac*w*coef*sign/(2*h)
                for j in range(3):
                    if sign==0:jets[3,i,comp,q,j,idx]=fac*w*coef*d[j]
        for j in range(3):
            jets[2,1,0,q,j,idx]=fac*w*d[j]
            jets[4,1,0,q,j,idx]=fac*w*d2[j]
        jets[5,1,0,q,0,idx]=fac*(dd+(2*ell+2)*dw/rx)
        jets[6,1,0,q,0,idx]=fac*(dd+2*ell*dw/rx+ell*(ell-1)*w/rx**2)
    obs=np.tensordot(rows(t),jets,axes=1)
    check_identity(obs,t)
    return obs

def check_identity(obs,t):
    terms=np.stack((obs[2],-obs[3],(1/t+1/(2*t**3))*obs[4],obs[5]/(3*t*t)))
    err=np.max(np.abs(terms.sum(0)))
    scale=np.max(np.abs(terms).sum(0))
    assert err<=1e-12*max(scale,1e-300),(err,scale)
    return err/max(scale,1e-300)

def check():
    for t in (1.,2.,12.):
        vel=-1/np.sqrt(1+np.linspace(t-.001,t+.001,7)**2)
        obs=receiver_bank(t,.053,.04,.008,.012,.001,vel,2,13,7)
        print(t,check_identity(obs,t))
        bad=obs.copy();bad[2]=0
        try:check_identity(bad,t)
        except AssertionError:pass
        else:raise AssertionError('negative control failed')
if __name__=='__main__':check()
