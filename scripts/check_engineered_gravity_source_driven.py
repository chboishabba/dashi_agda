"""Source-driven finite transfer, independent receiver, and F8 boundary socket.
Conditional linear models; no physical material or native continuum claim.
"""
import sympy as s


def eq(a,b=0):
    assert s.simplify(a-b)==0,(a,b)


def source_driven():
    # Positive scalar slab with independently specified left source J.
    # Outward Robin conditions: -p0+L*q0=J, p1+Z*q1=0.
    K,m,d,L,Z=s.symbols('K m d L Z',positive=True)
    J=s.symbols('J',real=True)
    C=s.cosh(m*d); S=s.sinh(m*d)
    P=s.Matrix([[C,S/(K*m)],[K*m*S,C]])
    den=P[1,0]+(L+Z)*C+L*Z*P[0,1]
    q0=J*(C+Z*P[0,1])/den
    p0=L*q0-J
    q1,p1=P*s.Matrix([q0,p0])
    eq(q1,J/den);eq(p1+Z*q1)
    eq(s.limit(den,m,0,dir='+'),L+Z+L*Z*d/K)
    assert den.is_positive
    # Field energy including both boundary impedances = J*q0/2.
    eq(q1*p1-q0*p0+L*q0*q0+Z*q1*q1,J*q0)
    # Reverse solve a target outgoing derivative flux, not free amplitude.
    target=s.symbols('target',real=True)
    eq((-p1).subs(J,target*den/Z),target)


def spherical():
    # Exact l=1 massless scalar conductivity analogue: shell a<r<b,
    # positive K contrast z, same interior/exterior K=1, imposed uniform
    # exterior gradient. Not a Poisson/Einstein material shield.
    a,b,z=s.symbols('a b z',positive=True)
    A,B,C,D=s.symbols('A B C D',real=True)
    # radial l=1 profiles Ar, Br+C/r², r+D/r².
    rows=[A*a-B*a-C/a**2,A-z*(B-2*C/a**3),
          B*b+C/b**2-b-D/b**2,z*(B-2*C/b**3)-1+2*D/b**3]
    sol=s.solve(rows,(A,B,C,D))
    f=(a/b)**3
    gain=9*z/(9*z+2*(z-1)**2*(1-f))
    eq(sol[A],gain)
    eq(gain.subs(z,1),1);eq(gain.subs(a,b),1)
    eq(gain.subs(z,1/z),gain)
    eq(s.limit(gain,z,s.oo),0)
    # Inverse target attenuation: z+1/z fixed, reciprocal branches.
    tau=s.symbols('tau',positive=True)
    eq((1/gain-1),2*(1-f)*(z+1/z-2)/9)
    # A finite positive contrast permits nonzero transmission only.
    # At a=b denominator degeneracy of shell geometry is taken by limit.


def f8_socket():
    # Exact current master flux owner uses C=(tk²f/3-t³j/3)Z.
    # Density/momentum owner rewrites it as -t³ Z Q on physical rows.
    t,k=s.symbols('t k',positive=True)
    f,j,Z,Q=s.symbols('f j Z Q',real=True)
    rel=s.solve(t*k*k*f/3-t**3*j/3+t**3*Q,f)[0]
    eq(((t*k*k*f/3-t**3*j/3)*Z).subs(f,rel),-t**3*Z*Q)
    # Retain independent sign, no k=0 inversion or physical gap claim.
    lam,eta=s.symbols('lam eta',positive=True)
    E=lam*Z*Z/2+eta*Q*Q/(2*lam)-t**3*Z*Q
    eq(E,lam*(Z-t**3*Q/lam)**2/2+(eta-t**6)*Q*Q/(2*lam))


if __name__=='__main__':
    for fn in (source_driven,spherical,f8_socket):
        fn();print('PASS',fn.__name__,flush=True)
    print('Conditional source-driven transfer only; physical background and original F8 continuum OPEN')
