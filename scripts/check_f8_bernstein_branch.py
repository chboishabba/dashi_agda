"""F8 branch restriction and Jensen integral using existing tensor controls."""
import sys,json
import numpy as np
from fractions import Fraction as Q
from check_f8_kernel_hermite_residual import I,D,U,rat,axis,stack
import check_f8_parameter_kernel as parent

def split(p,i):
    q=axis(p,i); l=[q[0]];r=[q[-1]]
    while len(q.l)>1:
        q=(q[:-1]+q[1:])*.5;l.append(q[0]);r.append(q[-1])
    def restore(a):
        return I(np.moveaxis(a.l,0,i),np.moveaxis(a.h,0,i))
    return restore(stack(l)),restore(stack(r[::-1]))

def stats(p,den):
    a=U(p.mag()/den);peak=np.max(a,axis=(0,1,2));s=U(a*a);m=s.shape[0]*s.shape[1];q=np.zeros(s.shape[2:])
    for i in range(s.shape[0]):
        for j in range(s.shape[1]):q=U(q+s[i,j])
    return peak,np.max(U(q/m),axis=0)

def restrict(num,below,z,h,w,depth):
    cut=rat(Q(1,13));zl=(z-h/2).l;zh=(z+h/2+w).h;cross=(zl<=cut.h)&(zh>=cut.l)
    den=D(np.maximum(cut.l,zl)**2);a,aa=stats(num,den);b,bb=stats(below,1.)
    peak=np.maximum(np.where(zh>=cut.l,a,0),np.where(zl<=cut.h,b,0));energy=np.maximum(np.where(zh>=cut.l,aa,0),np.where(zl<=cut.h,bb,0))
    # Crossing branch: sum of full integrals, not maximum of integrals.
    energy=np.where(cross,np.minimum(U(aa+bb),U(peak*peak)),energy)
    if depth and np.any(cross):
        P=num[:,:,:,cross];B=below[:,:,:,cross];Z=z[cross];peaks=[];energies=[]
        for ip,(p0,b0) in enumerate(zip(split(P,0),split(B,0))):
            for jp,(p1,b1) in enumerate(zip(split(p0,1),split(b0,1))):
                es=[];ps=[]
                for kp,(p2,b2) in enumerate(zip(split(p1,2),split(b1,2))):
                    zz=Z+(ip-jp)*h/4+kp*w/2
                    x,y=restrict(p2,b2,zz,h/2,w/2,depth-1);ps.append(x);es.append(y)
                peaks.append(np.maximum(*ps));energies.append(np.maximum(*es))
        pe=np.maximum.reduce(peaks);en=np.zeros_like(pe)
        for e in energies:en=U(en+e*.25)
        peak[cross]=np.minimum(peak[cross],pe);energy[cross]=np.minimum(energy[cross],en)
    return peak,energy

class Profile:
    candidate=staticmethod(parent.candidate)
    def __init__(self,depth):self.depth=depth;self.energies=[];self.base=[];self.cross=[]
    def envelope(self,p,q,z,h,w,zl,zh,k2,physical):
        cut=rat(Q(1,13));num=parent.mulz3(parent.mulz3(q,z,h,w),z,h,w)+rat(Q(15,4))*parent.elevsrc(parent.elevsrc(parent.elevate(parent.elevate(parent.elevate(parent.elevate(p,0),0),1),1)))
        below=q+rat(Q(15*13**2,4))*p;den=np.maximum(cut.l,zl)
        base=np.maximum(physical,np.where(zl<=cut.h,np.max(below.mag(),axis=(0,1,2)),0));peak,e=restrict(num,below,z,h,w,self.depth)
        peak=np.minimum(base,peak);e=np.minimum(e,U(peak*peak));self.base.append(base);self.energies.append(e);self.cross.append((zl<=cut.h)&(zh>=cut.l))
        return peak,U(k2.h+U(3.75/D(den*den)))

def symbolic():
    import sympy as S
    t=S.symbols('t');checks=0
    for n in (2,3,5):
        c=list(S.symbols('c:'+str(n+1)));B=lambda v:sum(a*S.binomial(n,i)*v**i*(1-v)**(n-i) for i,a in enumerate(c));q=c[:];l=[q[0]];r=[q[-1]]
        while len(q)>1:q=[(a+b)/2 for a,b in zip(q,q[1:])];l.append(q[0]);r.append(q[-1])
        for ctrl,v in ((l,t/2),(r[::-1],(1+t)/2)):
            assert S.expand(sum(a*S.binomial(n,i)*t**i*(1-t)**(n-i) for i,a in enumerate(ctrl))-B(v))==0;checks+=1
        for i in range(n+1):assert S.integrate(S.binomial(n,i)*t**i*(1-t)**(n-i),(t,0,1))==S.Rational(1,n+1);checks+=1
    # Unequal tensor degrees catch source-axis restoration errors.
    x=np.arange(4*5*3,dtype=float).reshape(4,5,3);p=I(x)
    for i in range(3):
        a,b=split(p,i);assert a.l.shape==b.l.shape==x.shape
        u=np.take(x,0,axis=i);v=np.take(x,-1,axis=i)
        assert np.all(np.take(a.l,0,axis=i)<=u) and np.all(np.take(a.h,0,axis=i)>=u)
        assert np.all(np.take(b.l,-1,axis=i)<=v) and np.all(np.take(b.h,-1,axis=i)>=v);checks+=1
    return checks

def run(n,mode,j,h,depth):
    profile=Profile(depth);oldprefix=parent.prefix
    def prefix(q):
        e=np.concatenate(profile.energies,axis=0);assert e.shape==q.shape
        return oldprefix(np.minimum(q,U(U(e*h)*h)))
    parent.prefix=prefix
    try:out=parent.run(n,mode,j,h,2,profile)
    finally:parent.prefix=oldprefix
    b=np.concatenate(profile.base,axis=0);e=np.concatenate(profile.energies,axis=0);c=np.concatenate(profile.cross,axis=0)
    out.update(depth=depth,checks=symbolic(),baseline_peak=float(b.max()),baseline_squared_sum_diagnostic=float(np.sum(b*b)),restricted_squared_sum_diagnostic=float(np.sum(e)),cross_baseline_fraction_diagnostic=float(np.sum(b[c]**2)/np.sum(b*b)),cross_restricted_fraction_diagnostic=float(np.sum(e[c])/np.sum(e)),scope='constant extension; selected whole source slab, all targets; branch restriction and Jensen integral; no receiver rerun')
    return out
if __name__=='__main__':print(json.dumps(run(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),2.**-int(sys.argv[4]),int(sys.argv[5]))))
