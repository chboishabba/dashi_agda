"""Scalar master boundary flux: exact cross-work, trace and frequency weights.
Conditional estimate, not a coupled embedding coercivity theorem.
"""
import sympy as s

def exact():
    t=s.symbols('t',positive=True); k=s.symbols('k',real=True)
    Z,f,j=[s.Function(a)(t) for a in ('Z','f','j')]
    Zt=s.diff(Z,t); ft=s.diff(f,t)
    # Interior n>=0, unit lapse and a=t at wall. Master energy has 1/2 normalization.
    Zn=(k*k*f/t**2-j)/3
    flux=-t**3*Zt*Zn
    alpha=t*k*k/3; beta=t**3*j/3
    # Add C=(alpha*f-beta)*Z, integrating the prescribed source work by parts too.
    C=(alpha*f-beta)*Z
    assert s.expand(flux+s.diff(C,t)-(alpha*ft+s.diff(alpha,t)*f-s.diff(beta,t))*Z)==0
    assert s.simplify((flux+s.diff(C,t)).subs(k,0)+s.diff(beta,t)*Z)==0
    # For any collar d and smooth real z, integrate derivative of (1-n/d)z².
    n,d=s.symbols('n d',positive=True); z=s.Function('z')(n)
    g=(1-n/d)*z*z
    assert s.expand(-s.diff(g,n)-z*z/d+2*(1-n/d)*z*s.diff(z,n))==0
    # Young at d: 2|z z'| <= z²/d + d z'².
    x,y=s.symbols('x y',real=True)
    assert s.expand(x*x/d+d*y*y-2*x*y-(x-d*y)**2/d)==0
    # Thus |Z(0)|² <= 2/d int Z² + d int Zn²; d=min(L,1/lambda).
    # With lambda>=1 and d=1/lambda, bound <= 2/lambda int (Zn²+lambda² Z²).
    a,c,lam=s.symbols('a c lam',nonnegative=True)
    assert s.expand((2/lam*(c+lam**2*a)-(2*lam*a+c/lam))*lam-c)==0
    # Frequency weight of coupling: alpha²/lambda ~ k³ at large k.
    # Positive completion of generic cross term |C| <= sqrt(E) sqrt(P).
    X,Y,theta=s.symbols('X Y theta',positive=True)
    assert s.expand(theta*X**2+Y**2/(4*theta)-X*Y-(2*theta*X-Y)**2/(4*theta))==0
    # This cannot be closed using only a k² f² wall energy uniformly in k.
    p=s.symbols('p',positive=True)
    assert s.limit(p**2/s.sqrt(1+p**2),p,s.oo)==s.oo
    # Exact signed modal complex work uses real parts of Hermitian products.
    Zr,Zi,fr,fi,gr,gi=s.symbols('Zr Zi fr fi gr gi',real=True)
    assert s.expand(s.re(s.conjugate(Zr+s.I*Zi)*((fr+s.I*fi)-(gr+s.I*gi)))-Zr*(fr-gr)-Zi*(fi-gi))==0
    # Mixed Israel compatibility removes f_t from the remaining work without 1/k.
    b=1/t; q=s.I*k*b
    W,u,V,K,w,jm=s.symbols('W u V K w jm')
    mixed=q*(W/2+ft-b*f)-3*(w*V+K*q*u)-jm
    R=alpha*ft+s.diff(alpha,t)*f
    replacement=2*k*k*f/3-t*k*k*W/6+t*K*k*k*u-t*w*q*V/b**2-t*q*jm/(3*b**2)
    assert s.expand(R-replacement+t*q*mixed/(3*b**2))==0
    assert replacement.subs(k,0)==0
    print('10 grouped checks PASS; exact master flux, mixed Israel and trace frequency budget')
    return C

if __name__=='__main__': exact()
