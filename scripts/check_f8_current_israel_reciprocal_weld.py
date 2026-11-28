"""F8 W2: exact physical GN master flux + Israel density/momentum reverse
correction. Retains temporal material-source derivative and homogeneous mode.
No unproved boundary trace, finite-band coercivity, or PDE continuation.
"""
import sympy as s

def exact():
    t,k=s.symbols('t k',positive=True)
    Z,f,j,A,P,M,mu=[s.Function(name)(t) for name in ('Z','f','j','A','P','M','mu')]
    # FRW/ GN master pressure-anisotropy wall normal derivative.
    Zn=(k*k*f/t**2-j)/3
    bulk_flux=-t**3*Z.diff(t)*Zn
    C=(t*k*k*f/3-t**3*j/3)*Z
    Q=A+M/(s.I*k)+j/3
    # Israel multiplied density-momentum equation k²/t² f=-3(A+M/(ik)).
    fisrael=-3*t*t*(A+M/(s.I*k))/k**2
    assert s.simplify((C+t**3*Q*Z).subs(f,fisrael))==0
    # No independent acceleration, pressure, or k²f_t source after transfer.
    W=s.simplify((bulk_flux+C.diff(t)).doit())
    assert s.simplify((W-((t*k*k*f/3-t**3*j/3).diff(t)*Z)).doit())==0
    assert s.simplify((W-(-t**3*Q).diff(t)*Z).subs(f,fisrael).doit())==0
    # Complex real/Hermitian polarization: flux and cross-work have identical signs.
    zr,zi,qr,qi=s.symbols('zr zi qr qi',real=True)
    cross=s.re(s.conjugate(zr+s.I*zi)*(qr+s.I*qi)).expand(complex=True)
    assert s.simplify(cross-zr*qr-zi*qi)==0
    # The true k=0 wall correction is -t³jZ/3, not the 1/k quotient.
    assert s.simplify(C.subs(k,0)+t**3*j*Z/3)==0
    # The smooth low-frequency continuation M(k)=k G(k) has finite quotient.
    kk=s.symbols('kk',real=True);a,b=s.symbols('a b',real=True)
    smooth=kk*(a+b*kk*kk)
    assert s.limit(smooth/(s.I*kk),kk,0)==-s.I*a
    # The temporal derivative of the material RHS is an actual obligation;
    # a fixed endpoint compatibility condition alone does not bound Q_t.
    assert s.diff(Q,t).has(s.diff(M,t))
    assert s.diff(Q,t).has(s.diff(A,t))
    print('PASS F8 current/Israel reciprocal boundary energy, source time jet and zero-frequency non-promotion')

if __name__=='__main__':exact()
