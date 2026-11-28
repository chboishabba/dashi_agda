"""Original G3 Gaussian vacuum fourth jet, numerical spatial derivatives.
No finite-time existence, interval certificate or material source claim.
"""
import numpy as np
from math import comb
from scipy.integrate import solve_ivp


def main():
    e=.25
    sol=solve_ivp(lambda r,y:[y[1],-16*e*e*y[0]/(3*(1+r*r)**4)],(0,64),(0.,1.),rtol=2e-13,atol=2e-15,dense_output=True)
    N=sol.y[1,-1]
    coeff=[1.]
    for n in range(8):
        coeff.append(-16*e*e/3*sum((-1)**j*comb(j+3,3)*coeff[n-j] for j in range(n+1))/((2*n+2)*(2*n+3)))
    def fields(X):
        r=np.linalg.norm(X); x,y,z=X; D=1+r*r
        if r<.1:
            v=r*r; P=sum(c*v**i for i,c in enumerate(coeff)); P1=sum(i*c*v**(i-1) for i,c in enumerate(coeff) if i); P2=sum(i*(i-1)*c*v**(i-2) for i,c in enumerate(coeff) if i>1)
            p=P/N; grad=2*P1/P*X; h=2*P1/P*r; H=2*P1/P*np.eye(3)+4*(P2/P-(P1/P)**2)*np.outer(X,X)
        else:
            u,up=sol.sol(r); p=u/(r*N); h=up/u-1/r; n=X/r
            grad=h*n; H=h/r*np.eye(3)+(-16*e*e/(3*D**4)-h*h-3*h/r)*np.outer(n,n)
        A=2*e*np.array([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/D**2
        B=4*A/D; b2=B@B
        # curl B=4 curl A/D + grad(4/D) cross A
        J=4*B/D-8*np.cross(X,A)/D**2
        Add=-(J+2*np.cross(grad,B))/p**2
        pdd=(-7*b2/12+h*h)/p
        gdd=b2*np.eye(3)-np.outer(B,B)+4*H-4*np.outer(grad,grad)+2*(np.trace(H)+2*h*h)*np.eye(3)
        def block(g,q,a):
            return np.block([[g+q*np.outer(a,a),(q*a)[:,None]],[(q*a)[None,:],np.array([[q]])]])
        h0=block(p*p*np.eye(3),p*p,A)
        qdd=2*p*pdd
        h2=block(gdd,qdd,A)
        h2[:3,:3]+=p*p*(np.outer(Add,A)+np.outer(A,Add))
        h2[:3,3]+=p*p*Add; h2[3,:3]+=p*p*Add
        return h0,h2
    def jets(X,d):
        f=np.array(fields(X)); first=np.zeros((2,4,4,4)); second=np.zeros((2,4,4,4,4)); E=np.eye(3)*d
        for i in range(3):
            a=np.array(fields(X+E[i])); b=np.array(fields(X-E[i])); first[:,i]=(a-b)/(2*d); second[:,i,i]=(a+b-2*f)/d**2
            for j in range(i):
                v=(np.array(fields(X+E[i]+E[j]))-np.array(fields(X+E[i]-E[j]))-np.array(fields(X-E[i]+E[j]))+np.array(fields(X-E[i]-E[j])))/(4*d*d)
                second[:,i,j]=second[:,j,i]=v
        return f,first,second
    def ric_and_variation(f,df,ddf):
        # Complex-step directional derivative of exact Ricci jet formula.
        def ric(g,dg,ddg):
            inv=np.linalg.inv(g); di=-np.einsum('ab,ibc,cd->iad',inv,dg,inv)
            C=np.empty((4,4,4),dtype=g.dtype); DC=np.empty((4,4,4,4),dtype=g.dtype)
            for a in range(4):
                for i in range(4):
                    for j in range(4):
                        v=dg[i,:,j]+dg[j,:,i]-dg[:,i,j]
                        C[a,i,j]=inv[a]@v/2
                        for k in range(4):
                            dv=ddg[k,i,:,j]+ddg[k,j,:,i]-ddg[k,:,i,j]
                            DC[k,a,i,j]=(di[k,a]@v+inv[a]@dv)/2
            return np.array([[sum(DC[a,a,i,j]-DC[j,a,i,a]+sum(C[a,a,b]*C[b,i,j]-C[a,j,b]*C[b,i,a] for b in range(4)) for a in range(4)) for j in range(4)] for i in range(4)])
        R=ric(f[0],df[0],ddf[0]); t=1e-20
        DR=ric(f[0]+1j*t*f[1],df[0]+1j*t*df[1],ddf[0]+1j*t*ddf[1]).imag/t
        return R,DR
    for X in (np.zeros(3),np.array([.5,.25,.75])):
        prev=None
        for d in (.008,.004,.002,.001):
            f,df,ddf=jets(X,d); g,h2=f; inv=np.linalg.inv(g); R,DR=ric_and_variation(f,df,ddf)
            h4=-2*DR-np.trace(inv@h2)*h2+2*h2@inv@h2
            defect=np.max(abs(h2+2*R)); trace=np.trace(inv@h2)
            # R_tt=-1/2 tr(g^-1 gtt)+1/4 tr((g^-1 gt)^2).
            # Its t² coefficient must vanish for vacuum.
            tt2=-np.trace(inv@h4)/4+np.trace(inv@h2@inv@h2)/2
            change=np.max(abs(h4-prev)) if prev is not None else float('nan')
            print('point',X.tolist(),'dx',d,'second-jet defect',defect,'trace',trace,'Rtt t² coefficient',tt2,'fourth change',change,flush=True)
            prev=h4
        assert defect<2e-4 and abs(trace)<1e-10 and abs(tt2)<2e-3 and change<.02
        print('fourth jet',h4.tolist(),flush=True)
    print('PASS numerical fourth-jet refinement; not interval or continuum acceptance')

if __name__=='__main__':main()
