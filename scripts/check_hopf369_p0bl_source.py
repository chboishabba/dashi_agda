"""BL: exact radial certificates of AN normalized covector derivative norms.
Angular reduction uses linearity in distinguished axis and SO(3) covariance.
"""
import sympy as s
from itertools import product


def radial_polys():
    x=s.symbols('x0:3',real=True);t,r=s.symbols('t r',real=True);h=s.Rational(4,5);eps=s.Rational(1,40)
    d=1-t;F=2*(1+t)/h;den=d**4+F**2*t;X=s.Matrix(x);e=s.Matrix([0,0,1]);z=x[2]
    # W=(delta^4-F^2 t)e+2F^2 z x+2F delta² e cross x.
    # This is exactly the original numerator for t=|x|².
    W=(d**4-F**2*t)*e+2*F**2*z*X+2*F*d*d*e.cross(X)
    a=eps*h*d*d*(F*d*W+(4*d/h+4*F)*X*(X.dot(W)))
    N={(k,):s.expand(a[k]) for k in range(3)}
    # Covariant derivative in gamma orthonormal frame. Each derivative
    # raises the denominator power by one; no division inside numerators.
    G=lambda k,i,j:h*(x[j]*int(k==i)-x[k]*int(i==j))
    def dd(N,p):
        out={}
        for i in range(3):
            for ix,f in N.items():
                df=s.diff(f,x[i])+2*x[i]*s.diff(f,t)
                corr=sum(G(k,i,j)*N[ix[:q]+(k,)+ix[q+1:]] for q,j in enumerate(ix) for k in range(3))
                out[(i,)+ix]=s.expand(h*d/2*(den*df-p*f*2*x[i]*s.diff(den,t))-den*corr)
        return out
    # Work polynomially until evaluating along the two angular extrema.
    for order in range(3):
        power=2+order;D=s.Poly(den.subs(t,r*r),r,domain=s.QQ)**(2*power)
        for axis in (0,2):
            sub={t:r*r,**{x[k]:r if k==axis else 0 for k in range(3)}}
            P=s.Poly(0,r,domain=s.QQ)
            for value in N.values():
                v=s.Poly(value.subs(sub,simultaneous=True),r,domain=s.QQ);P+=v*v
            yield order,axis,P,D
        if order<2:N=dd(N,power)


def certify():
    # Candidate bounds are deliberately rounded upward, not sample extrema.
    targets=[s.Rational(13,250),s.Rational(29,200),s.Rational(49,100)]
    for order,axis,P,D in radial_polys():
        # Exact rational polynomial test: if no roots on [0,1] and positive
        # at zero, target² D-P is strictly positive throughout.
        B=targets[order];R=B*B*D-P
        assert R.eval(0)>0 and R.eval(1)>0 and R.count_roots(0,1)==0
        # Diagnostic sampled max only; proof uses root count.
        import numpy as np
        fun=s.lambdify(P.gens[0],P.as_expr()/D.as_expr(),'numpy')
        sample=float(np.sqrt(np.max(fun(np.linspace(0,1,2001)))))
        print('order',order,'axis',axis,'certified norm bound',B,'sample max',sample,'degree',R.degree(),flush=True)

def divergence():
    r=s.symbols('r',real=True);t=r*r;h=s.Rational(4,5);eps=s.Rational(1,40);d=1-t
    V=32*eps*h*d*(t+1)*(4*h*h*d*d+t*t+6*t+1)/(h*h*d**4+4*t*(1+t)**2)**2
    v=h*h*d**3*r*V/4
    # Original exact BK divergence: x_3 replaces r; extremum at poles.
    num,den=s.fraction(s.cancel(s.Rational(13,100)**2-v*v));P=s.Poly(num,r,domain=s.QQ);D=s.Poly(den,r,domain=s.QQ)
    assert D.eval(0)>0 and D.count_roots(0,1)==0
    assert P.eval(0)>0 and P.eval(1)>0 and P.count_roots(0,1)==0
    print('PASS exact full-ball divergence norm < 13/100',flush=True)

if __name__=='__main__':certify();divergence()
