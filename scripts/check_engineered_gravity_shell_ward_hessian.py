"""Reciprocal shell: exact joint Hessian and controller/anchor Ward contract.
This is a local effective action identity, not an Einstein-matter solution.
"""
import sympy as s

def eq(a,b=0):
    assert s.simplify(a-b)==0,(a,b)

def main():
    # Gradient variables in any spatial direction, with q=phi'-X Z'.
    p,z,X,dp,dz,dX=s.symbols('p z X dp dz dX',real=True)
    t=s.symbols('t',real=True)
    E=((p-X*z)**2+z*z)/2
    H=s.diff(E.subs({p:p+t*dp,z:z+t*dz,X:X+t*dX},simultaneous=True),t,2).subs(t,0)
    eq(H,(dp-X*dz-z*dX)**2+dz**2-2*(p-X*z)*dz*dX)
    # Complete square with half the reference kinetic term reserved.
    q=p-X*z
    eq(dz**2-2*q*dz*dX, dz**2/2+(dz-2*q*dX)**2/2-2*q*q*dX*dX)
    # Exact same-action 1D static Ward including prescribed bias B=X0.
    x=s.symbols('x',real=True)
    P,Z,Y,B=[s.Function(v)(x) for v in ('phi','Z','X','B')]
    m,M=s.symbols('m M',positive=True)
    fields=[P,Z,Y,B]; deriv=[f.diff(x) for f in fields]
    W=((deriv[0]-Y*deriv[1])**2+deriv[1]**2+m*(P*P+Z*Z)+(deriv[2]-deriv[3])**2+M*(Y-B)**2)/2
    stress=sum(v*s.diff(W,v) for v in deriv)-W
    EL=[s.diff(W,f)-s.diff(s.diff(W,v),x) for f,v in zip(fields,deriv)]
    eq(stress.diff(x),-sum(e*v for e,v in zip(EL,deriv)))
    eq(EL[3],(Y-B).diff(x,2)-M*(Y-B))
    # With B prescribed, its residual is generally not zero even when
    # phi,Z,X solve their own equations. Add a dynamical support action
    # S_B and solve its equation, do not delete this term.
    assert EL[3]!=0
    # Exact zero-drive coercivity of potential block for |X|<=6:
    # det G=1, trace<=38, lambda_min>=1/trace>=1/38.
    G=s.Matrix([[1,-X],[-X,1+X*X]])
    eq(G.det(),1);eq(s.trace(G),2+X*X)
    # At finite drive, 2|q|^2<M leaves a positive order mass after
    # the above square completion. The actual field supremum must be
    # certified; finite quadrature samples do not establish this.
    print('PASS exact joint Hessian, zero-drive coercivity, and four-field Ward identity')
    print('OPEN actual bias/support equation, boundary stress, continuum inverse and Einstein coupling')
if __name__=='__main__':main()
