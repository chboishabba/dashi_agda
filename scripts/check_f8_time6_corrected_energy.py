"""F8 original 5th/6th-time energy: corrected inner work and outgoing budget.

True time-source F_m includes variable-GN commutator. Original inner
Neumann g_m=-6 Pi_m. Outer outgoing R=0 gives lower time-jet source;
those traces are supplied by triangular reconstruction in
check_f8_outgoing_triangular_weld.py. This proves algebraic conditional
energy bounds, NOT original source/initial/continuum estimates.
"""
import sympy as s


def exact():
    t,eta,eps,delta=s.symbols('t eta eps delta',positive=True)
    E4,E5,E6=s.symbols('E4 E5 E6',nonnegative=True)
    c0,c1=s.Rational(3500,3),s.Rational(1250,3)
    T5=c0*E4+c1*E5
    T6=c0*E5+c1*E6
    assert T5.subs({E4:0,E5:0})==0
    assert T6.subs({E5:0,E6:0})==0
    for m in (5,6):
        zz=s.Function(f'v{m}')(t)
        gg=s.Function(f'g{m}')(t)
        inner=-t**3*s.diff(zz,t)*gg
        D=t**3*zz*gg
        assert s.simplify(inner+s.diff(D,t)-zz*s.diff(t**3*gg,t))==0
    # Given |v_m(0)|²<=T_m the reciprocal correction obeys Young.
    T,z,g=s.symbols('T z g',nonnegative=True)
    assert s.simplify((delta*T+g*g/(4*delta)-z*g
         -(2*delta*z-g)**2/(4*delta)).subs(T,z*z))==0
    # Without Neumann source bound corrected energy is not positive.
    raw=s.symbols('raw',positive=True)
    G=s.symbols('G',positive=True)
    assert s.limit((raw-G).subs(raw,1),G,s.oo)==-s.oo
    B,N,go,q=s.symbols('B N go q',positive=True)
    flux=B*(go-N*q)*q
    assert s.simplify(flux+B*N*(q-go/(2*N))**2-B*go**2/(4*N))==0
    F,v,alpha=s.symbols('F v alpha',positive=True)
    assert s.simplify(alpha*v*v+F*F/(4*alpha)-v*F
                      -(2*alpha*v-F)**2/(4*alpha))==0
    pi5,pi6,pi7=s.symbols('pi5 pi6 pi7',real=True)
    assert s.diff(-6*t**3*pi5,t)==-18*t*t*pi5
    assert s.simplify(-6*(3*t*t*pi5+t**3*pi6))!=0
    assert s.simplify(-6*(3*t*t*pi6+t**3*pi7))!=0
    print('PASS F8 time5/6 corrected Neumann energies, trace debt, outgoing squares, source Young')
    print('OPEN: actual initial/commutator/source graph bounds, not source-free positivity')

if __name__=='__main__':exact()
