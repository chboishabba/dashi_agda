"""Exact cubic receiver for anchored massless reciprocal shell EFT.
Not a material realization, metric solution, or original F8 evolution.
"""
import sympy as s

def eq(a,b=0):
    assert s.simplify(a-b)==0,(a,b)

def main():
    r=s.symbols('r',positive=True); a=s.Rational(1,2)
    G=s.Matrix([[1,-6],[-6,37]]); H=s.Matrix([[0,-1],[-1,12]])
    A=s.Matrix([s.Rational(1,8),0]); C=(s.eye(2)-G.inv())*A/3
    q=(A-C)*r+C*a**3/r**2
    v=(q.diff(r).T*H*q.diff(r))[0]/2; w=(q.T*H*q)[0]/(2*r*r)
    F=[s.factor((v+2*w)/3),s.factor(2*(v-w)/3)]
    def lap(y,n):return y.diff(r,2)+2*y.diff(r)/r-n*(n+1)*y/r**2
    def particular(f,n):
        return (r**n*s.integrate(r**(1-n)*f,r)-r**(-n-1)*s.integrate(r**(n+2)*f,r))/(2*n+1)
    X=[]
    for n,f in zip((0,2),F):
        h=particular(f,n); u,v=s.symbols('u v')
        x=h+u*r**n+v*r**(-n-1)
        x=s.factor(x.subs(s.solve([x.subs(r,a),x.subs(r,1)],(u,v))))
        eq(lap(x,n),f);eq(x.subs(r,a));eq(x.subs(r,1));X.append(x)
    x0,x2=X
    S1=((r*r*x0*H*q.diff(r)).diff(r)-2*x0*H*q)/r**2
    S1+=s.Rational(2,5)*((r*r*x2*H*q.diff(r)).diff(r)+x2*H*q)/r**2
    S3=s.Rational(3,5)*((r*r*x2*H*q.diff(r)).diff(r)-4*x2*H*q)/r**2
    for n,S in ((1,S1),(3,S3)):
        rhs=(-G.inv()*S).applyfunc(s.expand)
        h=rhs.applyfunc(lambda f:particular(f,n))
        u=s.Matrix(s.symbols('u:2'));v=s.Matrix(s.symbols('v:2'))
        y=h+u*r**n+v*r**(-n-1)
        # Regular cavity and decaying exterior; deltaG vanishes at both anchors.
        rows=list(G*y.diff(r).subs(r,a)-n*y.subs(r,a)/a)+list(G*y.diff(r).subs(r,1)+(n+1)*y.subs(r,1))
        sol=s.solve(rows,list(u)+list(v));assert len(sol)==4
        y=y.subs(sol).applyfunc(s.simplify)
        for z in y.applyfunc(lambda z:lap(z,n))-rhs:eq(z)
        for z in G*y.diff(r).subs(r,a)-n*y.subs(r,a)/a:eq(z)
        for z in G*y.diff(r).subs(r,1)+(n+1)*y.subs(r,1):eq(z)
        cavity=(y.subs(r,a)/a**n).applyfunc(s.simplify)
        exterior=y.subs(r,1).applyfunc(s.simplify)
        print('mode',n,'cavity',cavity,'exterior',exterior,flush=True)
        print('cavity numeric',cavity.evalf(12),flush=True)
    print('PASS exact cubic field equation and both interface fluxes')

if __name__=='__main__':main()
