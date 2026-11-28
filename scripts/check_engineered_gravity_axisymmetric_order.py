"""Leading axisymmetric order/field correction and residual norm.
Conditional EFT on a finite annulus; not the original F8 tensor solver.
"""
import sympy as s

def eq(a,b=0):
    assert s.factor(s.simplify(a-b))==0,(a,b)

def main():
    r=s.symbols('r',positive=True)
    mu=s.symbols('mu',real=True)
    P=lambda n:s.legendre(n,mu)
    project=lambda f,n:s.expand((2*n+1)*s.integrate(s.expand(f*P(n)),(mu,-1,1))/2)
    eq(P(2)*P(1),2*P(1)/5+3*P(3)/5)
    eq(s.diff((1-mu**2)*P(2)*s.diff(P(1),mu),mu),2*P(1)/5-12*P(3)/5)
    # Existing sharp-shell source; retain the actual radial functions.
    G=s.Matrix([[1,-6],[-6,37]])
    Gx=s.Matrix([[0,-1],[-1,12]])
    A=s.Matrix([s.Rational(1,8),0])
    C=(s.eye(2)-G.inv())*A/3
    B=A-C
    q=B*r+C/(8*r**2)
    a=(q.diff(r).T*Gx*q.diff(r))[0]/2
    b=(q.T*Gx*q)[0]/(2*r*r)
    F0=s.factor((a+2*b)/3); F2=s.factor(2*(a-b)/3)
    print('actual sharp shell F0,F2:',F0,F2)
    print('actual F2 at 3/4:',F2.subs(r,s.Rational(3,4)))
    # Solve leading order material response with finite annulus Dirichlet
    # anchoring and zero order mass (a specific comparator, not free wall).
    solutions=[]
    for n,F in ((0,F0),(2,F2)):
        # variation of parameters for Laplacian X=F, with r^n,r^(-n-1).
        h=r**n*s.integrate(r**(1-n)*F,r)/(2*n+1)-r**(-n-1)*s.integrate(r**(n+2)*F,r)/(2*n+1)
        a0,b0=s.symbols('a0 b0')
        x=h+a0*r**n+b0*r**(-n-1)
        x=s.simplify(x.subs(s.solve([x.subs(r,s.Rational(1,2)),x.subs(r,1)],(a0,b0))))
        eq(s.diff(x,r,2)+2*s.diff(x,r)/r-n*(n+1)*x/r**2,F)
        eq(x.subs(r,s.Rational(1,2)));eq(x.subs(r,1))
        solutions.append(x)
    # Field source at cubic order, divergence of deltaG grad(q P1).
    x0,x2=solutions
    source1=((r*r*x0*Gx*q.diff(r)).diff(r)-2*x0*Gx*q)/r**2
    source1+=((r*r*x2*Gx*q.diff(r)).diff(r)+x2*Gx*q)/r**2*s.Rational(2,5)
    source3=((r*r*x2*Gx*q.diff(r)).diff(r)-4*x2*Gx*q)/r**2*s.Rational(3,5)
    src=((r*r*(x0+x2*P(2))*Gx*q.diff(r)).diff(r)*P(1)+(x0*Gx*q)*s.diff((1-mu**2)*s.diff(P(1),mu),mu)+x2*Gx*q*s.diff((1-mu**2)*P(2)*s.diff(P(1),mu),mu))/r**2
    for i in range(2):
        eq(src[i],source1[i]*P(1)+source3[i]*P(3))
        eq(project(src[i],5))
    # Orthogonal angular norm of omitted source; exact, not continuum
    # convergence. For the leading source there is no l>=5 residual.
    for n in range(6):
        eq(project(P(n),n),1)
    print('PASS anchored leading order material solutions, cubic field source projection, angular parity')
    print('OPEN cubic field BVP, smooth background, massive coefficients, metric/controller stress, original F8')

if __name__=='__main__':main()
