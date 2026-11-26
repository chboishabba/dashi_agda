"""BK: indicial ground-state identity and tapered BG trial, not a global inverse."""
from check_hopf369_p0bh import *
from check_hopf369_p0bj import Wfun
from check_hopf369_p0bj_compact import QB
import sympy as s

def exact():
    y,h,p,r=s.symbols('y h p r',positive=True); b,bp=s.symbols('b bp',positive=True)
    z=s.Function('z')(y); B=s.Function('b')(y)
    normal=lambda q:-s.diff(B**3*s.diff(q,y),y)+4*B**3*q
    assert s.simplify(normal(B*z)-z*normal(B)+s.diff(B**5*s.diff(z,y),y)/B)==0
    assert s.expand((-b**4-3*b*b*bp**2+4*b**4).subs(bp**2,b*b-h*h)-3*h*h*b*b)==0
    delta=1-r*r; v=delta**p
    lap=h*h*delta**2/4*(s.diff(v,r,2)+2/r*s.diff(v,r)+2*r/delta*s.diff(v,r))
    assert s.simplify(lap/v-h*h*p*(-s.Rational(3,2)*delta+(p-2)*r*r))==0
    assert s.expand(3-p*(p-2)+(p-3)*(p+1))==0
    assert 6*s.Rational(16,25)*(3-s.Rational(5,2)*s.Rational(1,2))==s.Rational(168,25)
    print('PASS normal ground state, indicial exponents -1 and 3, p=5/2 margin 168/25',flush=True)
    # Exact AN covector divergence in the Poincare metric. t=|x|^2.
    t,e=s.symbols('t e',real=True);delta=1-t;F=2*(1+t)/h;D=delta**4+F**2*t
    A=2*e*(2*F**3*delta/D**2+(4*delta/h+4*F)/D)
    B=2*e*F*delta*(delta**4-F**2*t)/D**2
    V=4*A+2*t*s.diff(A,t)+2*s.diff(B,t)
    den=h*h*delta**4+4*t*(1+t)**2
    target=32*e*h*delta*(t+1)*(4*h*h*delta**2+t*t+6*t+1)/den**2
    assert s.cancel(V-target)==0
    assert s.simplify(s.limit(V/delta,t,1)-2*e*h)==0
    # div_gamma a = h^2 delta^3 x_3 V/4, hence O(delta^4).
    print('PASS exact AN divergence cancellation at orders delta^2 and delta^3',flush=True)

def product_jets(q,v,d,dd):
    out=q*v[:,None];out[:,1:5]+=d*q[:,:1]
    out[:,5:]+=(dd*q[:,0,None,None]+d[:,:,None]*q[:,None,1:5]+q[:,1:5,None]*d[:,None,:]).reshape(-1,16)
    return out

def taper(X,q,k):
    if k==0:return q.copy()
    x=X[:,:3];r=np.sum(x*x,axis=1);v=1-r**k
    d=np.zeros((len(X),4));d[:,:3]=-2*k*r[:,None]**(k-1)*x
    dd=np.zeros((len(X),4,4));dd[:,:3,:3]=-2*k*r[:,None,None]**(k-1)*np.eye(3)-4*k*(k-1)*r[:,None,None]**(k-2)*x[:,:,None]*x[:,None,:]
    return product_jets(q,v,d,dd)

def weight52(X,psi):
    x=X[:,:3];v=np.sqrt(1-np.sum(x*x,axis=1))
    d=np.zeros((len(X),4));d[:,:3]=-x/v[:,None]
    dd=np.zeros((len(X),4,4));dd[:,:3,:3]=-np.eye(3)/v[:,None,None]-x[:,:,None]*x[:,None,:]/v[:,None,None]**3
    return product_jets(psi,v,d,dd)

def run(c):
    base=sample(10,456);q=sample(7,814);x=q[:,:3]/np.linalg.norm(q[:,:3],axis=1)[:,None]
    X=np.vstack([base,*[np.c_[x*r,q[:,3]] for r in (.9,.99,.999,.9999)]]);eps=.025;ks=(0,2,4,8,16,32,64);rows={k:[] for k in ks}
    for i in range(0,len(X),128):
        xx=X[i:i+128];B,q=evaluate_points(xx,eps,c);psi=np.asarray(Wfun(j.array(xx),eps));p52=weight52(xx,psi)
        for k in ks:
            v=taper(xx,q,k);F=np.asarray(Rbatch(*B,v));D=np.asarray(DJ(*B,v));rows[k].append(np.c_[F,F/psi[:,0],F/p52[:,0],-np.sum(D*p52,axis=1)/p52[:,0]])
    for k in ks:
        a=np.concatenate(rows[k]);print('taper',k,'bulk RMS',np.sqrt(np.mean(a[:1024,0]**2)),'weighted2 bulk max',np.max(abs(a[:1024,1])),'weighted2.5 bulk max',np.max(abs(a[:1024,2])),'tail2.5 layer maxima',[float(np.max(abs(a[1024+i*128:1024+(i+1)*128,2]))) for i in range(4)],'min p2.5 margin',a[:,3].min(),flush=True)
    x=sample(5,987)[:,:3];Z=np.vstack([np.c_[x,np.zeros(len(x))],np.c_[x,np.full(len(x),L)]]);B,q=evaluate_points(Z,eps,c);N=len(x)
    for k in (0,8,32):
        r,g,I,G,Ric=map(np.asarray,Ebatch(*B,taper(Z,q,k)));K=-G[:,3,:3,:3]/np.sqrt(I[:,3,3,None,None]);H=g[:N,:3,:3];Hi=np.linalg.inv(H);M=(K[:N]+K[N:])/2
        J2=-(Ric[:N,:3,:3]-Ric[N:,:3,:3])+J*M-J*np.trace(Hi@M,axis1=1,axis2=2)[:,None,None]*H
        mixed=Hi@J2;tf=mixed-np.trace(mixed,axis1=1,axis2=2)[:,None,None]*np.eye(3)/3
        first=np.max(abs(Hi@(K[:N]-K[N:]-J*H)));second=np.max(abs(tf));print('seam taper',k,'first',first,'TF',second,'scalar max',np.max(abs(r)),flush=True);assert first<1e-8 and second<1e-8
    Z=X[:128];B,q=evaluate_points(Z,eps,c);pos=np.asarray(Rbatch(*B,taper(Z,q,8)));neg=c.copy();neg[:180].reshape(9,4,5)[:,:,[2,4]]*=-1;neg[180:]=c[180:].reshape(9,4,2)[:,:,::-1].ravel();R=Z.copy();R[:,3]=L-R[:,3]
    B,q=evaluate_points(R,-eps,neg);minus=np.asarray(Rbatch(*B,taper(R,q,8)));B,q=evaluate_points(Z,0.,np.zeros_like(c));zero=np.asarray(Rbatch(*B,taper(Z,q,8)))
    print('signed scalar discrepancy',np.max(abs(pos-minus)),'zero scalar max',np.max(abs(zero)),flush=True);assert np.max(abs(pos-minus))<1e-8 and np.max(abs(zero))<1e-8
    # Seed only: regular quotient T(0)/(f0 delta^2), evaluated directly
    # at the boundary and approaching it. Its exact decay is O(delta^2).
    S=sample(4,927);n=S[:,:3]/np.linalg.norm(S[:,:3],axis=1)[:,None]
    X=np.vstack([np.c_[n*r,S[:,3]] for r in (.9,.99,.999,.9999,1.)]);z=np.zeros_like(c)
    a=np.asarray(QB(j.array(X),eps,z,0.)).reshape(5,-1)
    print('seed compactified quotient layer maxima',np.max(abs(a),axis=1),flush=True)
    print('seed quotient / delta^2 maxima',np.max(abs(a[:4]),axis=1)/(1-np.array([.9,.99,.999,.9999])**2)**2,flush=True)
    assert np.max(abs(a[-1]))<1e-10 and np.max(abs(a[-2]))<np.max(abs(a[-3]))/50


if __name__=='__main__':
    exact();c=np.array(json.loads(Path(sys.argv[1]).read_text().split('COEFFICIENTS ')[-1]));assert len(c)==252;run(c)
