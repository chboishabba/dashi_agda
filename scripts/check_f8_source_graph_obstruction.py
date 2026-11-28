"""Original l=0 conservative TT source: exact origin obstruction and high-precision sweep.
No replacement of the original cell-average source. Independent evaluation of
its p0 primitive; no production propagation or kernel claim.
"""
import json
from functools import lru_cache
import sympy as s
import mpmath as mp


def exact():
    u=s.symbols('u');f=s.exp(1-1/(1-u*u))
    p=s.Rational(2,5)*(u*u*s.diff(f,u,3)+2*u*s.diff(f,u,2)-2*s.diff(f,u))
    g=s.diff(p,u)/u**2
    assert s.series(g,u,0,4).removeO()==-24-56*u*u
    d=3
    @lru_cache(None)
    def B(k,j):
        a=max(s.S.Zero,s.Rational(2*j-1,2));b=s.Rational(2*j+1,2)
        if k==0:return s.Rational(d,d+2)*(b**(d+2)-a**(d+2))/(b**d-a**d)
        if j==0:return -2*d*(B(k-1,1)-B(k-1,0))
        den=b**d-a**d;cp=d*b**(d-1)/den;cm=d*a**(d-1)/den
        return -cp*(B(k-1,j+1)-B(k-1,j))+cm*(B(k-1,j)-B(k-1,j-1))
    assert B(2,0)==-s.Rational(373248,41405)
    c=-56*B(2,0)
    assert c>0
    return p,g,u,c


def sweep():
    p,g,u,c=exact();mp.mp.dps=75
    P=s.lambdify(u,p,'mpmath');G=s.lambdify(u,g,'mpmath')
    eps=mp.mpf('.04');rows=[]
    for n in (16,32,64,128,256,512):
        h=eps/n;nr=3*n
        cells=[(max(mp.mpf(0),(mp.mpf(j)-mp.mpf('.5'))*h),(mp.mpf(j)+mp.mpf('.5'))*h) for j in range(nr)]
        w=[(b**3-a**3)/3 for a,b in cells]
        def primitive(x):return mp.mpf(0) if x<=0 or x>=1 else P(x)
        fv=[eps**3*(primitive(b/eps)-primitive(a/eps))/v if a<eps else mp.mpf(0) for (a,b),v in zip(cells,w)]
        point=[mp.mpf(-24) if j==0 else (G(j*h/eps) if j<n else mp.mpf(0)) for j in range(nr)]
        def A(x):
            out=[-6*(x[1]-x[0])/h**2]
            for j in range(1,nr):
                a,b=cells[j];nxt=x[j+1] if j+1<nr else 0
                out.append((-b*b*(nxt-x[j])+a*a*(x[j]-x[j-1]))/(w[j]*h))
            return out
        def norm(x):return mp.sqrt(mp.fsum(v*z*z for v,z in zip(w,x)))
        def norms(x):
            y=A(x);z=A(y)
            return [float(norm(x)),float(mp.sqrt(mp.fsum(v*a*b for v,a,b in zip(w,x,y)))),float(norm(y)),float(mp.sqrt(mp.fsum(v*a*b for v,a,b in zip(w,y,z)))),float(norm(z))],z
        fn,z=norms(fv);pn,_=norms(point)
        origin=h*h*eps*eps*z[0];expected=mp.mpf(str(s.N(c,72)))
        rows.append(dict(n=n,h=float(h),fv=fn,point=pn,origin_scaled=float(origin),origin_rel=float(abs(origin-expected)/expected),lower_bound_scaled=float(mp.sqrt(h)*mp.sqrt(w[0])*abs(z[0]))))
    assert rows[-1]['origin_rel']<1e-4
    assert rows[-1]['origin_rel']<rows[0]['origin_rel']
    return dict(origin_coefficient=str(c),orders=[0,.5,1,1.5,2],precision=mp.mp.dps,rows=rows)


if __name__=='__main__':print(json.dumps(sweep(),indent=2))
