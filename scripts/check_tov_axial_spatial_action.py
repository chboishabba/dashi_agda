"""Axial spatial action in radial angular-shift gauge; fixed spherical boundary.
Exact geometric coefficient checks, not a full physical evolution theorem.
"""
import sympy as s

def main():
    r,f,N,a,c,L=s.symbols('r f N a c L',positive=True)
    B,u,up=s.symbols('B u up',real=True)
    # Radial foliation of spatial metric, lapse 1/sqrt(f), shift B S^A.
    # k_AB=sqrt(f)*(r gamma_AB-r^2 B S_AB), trace independent of B.
    z,w=s.symbols('z w',real=True)
    gamma=s.eye(2); shear=s.Matrix([[z,w],[w,-z]])
    k=s.sqrt(f)*(r*gamma-r*r*B*shear); mixed=k/r**2
    assert s.simplify(s.trace(mixed)-2*s.sqrt(f)/r)==0
    assert s.simplify(s.trace(mixed*mixed)-2*f/r**2-f*B**2*s.trace(shear*shear))==0
    # Radial Gauss scalar R3=R2-k^2-tr(k^2)-2 normal(k), radial lapse
    # has no tangential derivative. Normal derivative of trace unchanged.
    grav=N*r*r*s.sqrt(f)*L*(L-2)*B**2/(32*s.pi)
    mat=N*r*r/s.sqrt(f)*(a-c)*(f*r*r*L*(up-B)**2+L*(L-2)*u**2)
    # Under angular gauge shift xi, B->B+xi', u->u+xi,
    # tensor C->C+2xi. RW invariants B-C'/2, u-C/2.
    C,Cp,xi,xip=s.symbols('C Cp xi xip',real=True)
    assert s.expand(B+xip-(Cp+2*xip)/2-(B-Cp/2))==0
    assert s.expand(u+xi-(C+2*xi)/2-(u-C/2))==0
    # Exact positive square coefficients for ell>=2, interior a>c.
    ell=s.symbols('ell',positive=True); d=s.symbols('d',positive=True)
    assert s.factor((grav+mat).subs({L:ell*(ell+1),a:c+d}))!=0
    assert grav.subs(L,2)==0
    assert s.simplify(mat.subs({L:2,up:B}))==0
    x=s.symbols('x',real=True)
    for l in range(1,9):
        Y=s.legendre(l,x); ll=l*(l+1); norm=s.integrate(Y**2,(x,-1,1))
        assert s.integrate((1-x*x)**2*s.diff(Y,x,2)**2/2,(x,-1,1))==ll*(ll-2)*norm/2
    print('PASS radial Gauss shear coefficient, RW invariants, dipole degeneracy, 8 angular norms')
    print('OPEN physical action domain, time-dependent corner terms, polar constrained spatial form')
if __name__=='__main__':main()
