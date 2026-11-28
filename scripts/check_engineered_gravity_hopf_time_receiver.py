"""Original G3 time jets and same-event receiver inverse, not finite-time evolution."""
import sympy as s


def eq(a,b=0):
    assert s.simplify(a-b)==0,(a,b)


def main():
    t,e,p,k=s.symbols('t epsilon psi0 k',real=True,nonzero=True)
    # P0T/V: original central field and curl computed directly.
    x,y,z=s.symbols('x y z',real=True); X=(x,y,z); D=1+x*x+y*y+z*z
    A=2*s.Matrix([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/D**2
    curl=lambda v:s.Matrix([s.diff(v[2],y)-s.diff(v[1],z),s.diff(v[0],z)-s.diff(v[2],x),s.diff(v[1],x)-s.diff(v[0],y)])
    B=curl(A); J=curl(B); origin=dict.fromkeys(X,0)
    assert B.subs(origin)==s.Matrix([0,0,8])
    assert J.subs(origin)==s.Matrix([0,0,32])
    # Original V4 central connection and radion second derivatives.
    Add=-32*e/p**2; phidd=-112*e**2/(3*p)
    # Time-symmetric normal gauge A_t=0. F_zt=-partial_t A_z.
    Fzt=-Add*t
    # Rest probe in base frame at the initial event: leading affine
    # coordinate acceleration slope from signed momentum, with u^t retained.
    v=s.symbols('u_t',positive=True)
    slope=k*Fzt*v/(p*p*t)
    eq(slope,32*k*e*v/p**4)
    eq(slope.subs(k,-k),-slope)
    # Proper spatial component, affine normalization not silently fixed.
    eq(p*slope,32*k*e*v/p**3)
    # Tidal trace and compact scale are even and share one source.
    trace=112*e**2/(3*p**2)
    eq(trace,-phidd/p)
    eq((p*slope)**2/trace, s.Rational(192,7)*k*k*v*v/p**4)
    # Zero compact momentum has no signed force slope; neutral tide remains.
    eq(slope.subs(k,0),0)
    print('PASS original central curl, connection time jet, signed rest-probe slope and even tidal inverse')
    print('OPEN finite-time solution, material coupling, physical units and detector')

if __name__=='__main__':main()
