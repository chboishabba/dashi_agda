"""F8 parameter-polynomial residual on complete source slabs.
Uses existing characteristic recurrence and signed Bernstein owner. No
source-position differentiability assumption, including at auxiliary cutoff.
"""
import json,sys,time
from fractions import Fraction as Q
import numpy as np
from check_f8_global_wall_kernel import clock,grid,derivatives
from check_f8_kernel_hermite_residual import I,D,U,rat,stack,axis,elev,elevate,diff,hermite,mulz,pi_box,prefix

def backsrc(p):return I(np.moveaxis(p.l,0,2),np.moveaxis(p.h,0,2))
def elevsrc(p):
    q=axis(p,2);return backsrc(elev(q,len(q.l)-1))

def muls(p):
    q=axis(p,2);n=len(q.l)-1
    return backsrc(stack([q[0]*0]+[q[j-1]*rat(Q(j,n+1)) for j in range(1,n+2)]))

def mulz3(p,z,h,w):
    # z=z_left+h(x-y)/2+w*s. Preserve all signed polynomial coefficients.
    return elevsrc(mulz(p,z,h))+w*muls(elevate(elevate(p,0),1))

def candidate(xi,k,h,na,nb):
    # Existing literal recurrence, Richardson only proposes reconstruction jets.
    r=grid(xi,k,h,na,nb);a,b=derivatives(r,xi,k,h)
    f=grid(xi,k,h/2,2*na,2*nb);fa,fb=derivatives(f,xi,k,h/2)
    r,a,b=[(4*f0[::2,::2]-c)/3 for f0,c in ((f,r),(fa,a),(fb,b))]
    z=np.maximum(1/13,xi+(np.arange(na+1)[:,None]-np.arange(nb+1)[None,:])*h/2)
    assert np.all(r[0]==1) and np.all(r[:,0]==1) and not np.any(a[:,0]) and not np.any(b[0])
    return r,a,b,-(k*k+3.75/z**2)*r/4

def hull(p):return np.min(p.l,axis=(0,1,2)),np.max(p.h,axis=(0,1,2))
def sumup(x):
    t=0.
    for a in x:t=U(t+a)
    return t

def run(n,mode,j,h,degree):
    st=time.monotonic();dt,t,b,lo,hi,span=clock(n);xi=I(lo[j],hi[j+1]);w=I(float(xi.h))-I(float(xi.l));cut=rat(Q(1,13));k=mode*np.pi/3.012;pl,ph=pi_box();K=I(D(float(mode*pl/Q('3.012'))),U(float(mode*ph/Q('3.012'))));K2=K*K
    boxes=[]
    for i in range(n):
        lag=I(max(0,abs(i-j)-1),abs(i-j)+1)*dt;dz=I(lo[i],hi[i+1])-xi;A=lag+dz;B=lag-dz;boxes.append((I(max(0,A.l),A.h),I(max(0,B.l),B.h)))
    na=int(max(a.h for a,b in boxes)/h)+2;nb=int(max(b.h for a,b in boxes)/h)+2
    mid=float((xi.l+xi.h)/2);points=[mid] if degree==0 else [float(xi.l),mid,float(xi.h)]
    jets=[candidate(x,k,h,na,nb) for x in points];res=np.empty((na,nb));V=np.empty_like(res);ranges=np.empty((3,2,na,nb));cross=0
    for start in range(0,na,8):
        stop=min(na,start+8);p=[hermite(*(v[start:stop+1] for v in row),h) for row in jets]
        # Exact source Bernstein polynomial. Midpoint is a proposed literal
        # reconstruction, not assumed to equal the exact kernel there.
        p=stack(p if degree==0 else [p[0],2*p[1]-(p[0]+p[2])/2,p[2]],2)
        ab=elevate(elevate(diff(diff(p,0,h),1,h),0),1);q=4*ab+K2*p
        z0=I(float(xi.l))+I((np.arange(start,stop)[:,None]-np.arange(nb)[None,:])*h/2)
        zl=(z0-h/2).l;zh=(z0+h/2+w).h
        num=mulz3(mulz3(q,z0,h,w),z0,h,w)+rat(Q(15,4))*elevsrc(elevsrc(elevate(elevate(elevate(elevate(p,0),0),1),1)))
        den=np.maximum(cut.l,zl);above=U(np.max(num.mag(),axis=(0,1,2))/D(den*den));below=np.max((q+rat(Q(15*13**2,4))*p).mag(),axis=(0,1,2));res[start:stop]=np.maximum(np.where(zh>=cut.l,above,0),np.where(zl<=cut.h,below,0));V[start:stop]=U(K2.h+U(3.75/D(den*den)));cross+=int(np.sum((zh>=cut.l)&(zl<=cut.h)))
        for m,poly in enumerate((p,diff(p,0,h),diff(p,1,h))):ranges[m,0,start:stop],ranges[m,1,start:stop]=hull(poly)
    F2=prefix(U(U(res*res)*h*h));rows=[]
    for i,(A,B) in enumerate(boxes):
        ai=max(0,int(np.floor(A.l/h)));aj=int(np.floor(A.h/h));bi=max(0,int(np.floor(B.l/h)));bj=int(np.floor(B.h/h));T=U(U(A.h+B.h)/2);f2=F2[aj,bj];E=U(T*U(np.sqrt(U(f2/2))))
        def der(f,v):
            ff=U(sumup(f)*h);vv=U(sumup(v)*h);return U((I(ff)+I(U(np.sqrt(U(U(vv*T)*f2))))).h/4)
        ea=der(np.max(res[ai:aj+1,:bj+1],axis=0),np.max(V[ai:aj+1,:bj+1],axis=0));eb=der(np.max(res[:aj+1,bi:bj+1],axis=1),np.max(V[:aj+1,bi:bj+1],axis=1))
        bnd=[]
        for m,e in enumerate((E,ea,eb)):
            bnd.append(I(D(np.min(ranges[m,0,ai:aj+1,bi:bj+1])-e),U(np.max(ranges[m,1,ai:aj+1,bi:bj+1])+e)))
        out=[bnd[0]/2,(bnd[1]+bnd[2])/2,(bnd[1]-bnd[2])/2]
        rows.append(dict(target=i,value_error=float(U(E/2)),derivative_error=float(U(U(ea+eb)/2)),bounds=[[float(x.l),float(x.h)] for x in out]))
    return dict(n=n,mode=mode,source=j,degree=degree,h=h,xi=[float(xi.l),float(xi.h)],cells=na*nb,cutoff_crossing_cells=cross,max_residual=float(res.max()),seconds=time.monotonic()-st,rows=rows,scope='whole selected source slab and every target slab; conditional outward residual, no receiver or continuous inverse rerun')

def symbolic():
    import sympy as S
    s,x,y,z,w,h=S.symbols('s x y z w h');checks=0
    for n in range(5):
        c=S.symbols('c:'+str(n+1));B=lambda n,i:S.binomial(n,i)*s**i*(1-s)**(n-i)
        p=sum(c[i]*B(n,i) for i in range(n+1));p1=sum(c[i-1]*S.Rational(i,n+1)*B(n+1,i) for i in range(1,n+2));assert S.expand(s*p-p1)==0;checks+=1
    a,b,c=S.symbols('a b c');p=a*(1-s)**2+2*(2*b-(a+c)/2)*s*(1-s)+c*s*s
    assert p.subs(s,0)==a and p.subs(s,S.Rational(1,2))==b and p.subs(s,1)==c;checks+=3
    A,B,xi,k=S.symbols('A B xi k');R=S.Function('R')(A,B,xi);zz=xi+(A-B)/2
    assert S.simplify(zz**2*(4*S.diff(R,A,B)+(k*k+S.Rational(15,4)/zz**2)*R)- (zz**2*(4*S.diff(R,A,B)+k*k*R)+S.Rational(15,4)*R))==0;checks+=1
    return checks
if __name__=='__main__':print(json.dumps(dict(symbolic_checks=symbolic(),**run(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),2.**-int(sys.argv[4]),int(sys.argv[5])))),flush=True)
