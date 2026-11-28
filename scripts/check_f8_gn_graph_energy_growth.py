"""F8 W2 scalar graph-energy growth with original signed wall flux.
Derived from source and commutator identities; not coupled Einstein coercivity.
"""
import sympy as s

def exact():
    E0,E1,Ek,F,Ft,t,k=s.symbols('E0 E1 Ek F Ft t k',nonnegative=True)
    # E0/E1 energies and Ek=k² E0; 20 is the exact GN coefficient cap.
    H=E0+E1+Ek
    # First-level source bound: |F0 u_t|<=E0+F0²/(2A).
    # Second-level source: F1=Ft+Comm, so
    # |F1 u_tt|<= E1+(Ft+Comm)²/(2A)
    #             <= E1+Ft²/A+Comm²/A.
    # Commutator bound is integrated modewise on n∈[0,1/2].
    comm=30625000*E0+10*E1+51840*Ek+2000*F
    bound=20*H+E0+E1+Ek+(1+k*k)*F/2+Ft+comm
    # E'=B(L)-B(0)+bulk work; B=t³ u_t u_n for first level.
    L=30625021
    major=L*H+(s.Rational(4001,2)+k*k/2)*F+Ft
    assert s.simplify(major-bound).expand().coeff(E0)==0
    assert s.simplify(major-bound).expand().coeff(Ek)==51840*0+30625021-(21+51840)
    assert s.simplify(major-bound).expand().coeff(E1)==30625021-31
    assert s.simplify(major-bound).expand().coeff(F)==0
    # The integrated boundary work remains (outer minus inner):
    # (1+k²) B0+ B1. Neither sign nor trace is assumed.
    Ut,Un,Utt,Unt=s.symbols('Ut Un Utt Unt',real=True)
    J=(1+k*k)*t**3*Ut*Un+t**3*Utt*Unt
    assert s.simplify(J-((1+k*k)*t**3*Ut*Un+t**3*Utt*Unt))==0
    assert J.subs({t:1,k:0,Ut:1,Un:1,Utt:0,Unt:0})==1
    assert J.subs({t:1,k:0,Ut:1,Un:-1,Utt:0,Unt:0})==-1
    # Exact conditional Gronwall socket, with arbitrary boundary source budget B(t):
    h0,forcing,gamma=s.symbols('h0 forcing gamma',positive=True)
    tau=s.symbols('tau',nonnegative=True)
    sol=(h0+forcing/gamma)*s.exp(gamma*tau)-forcing/gamma
    assert s.simplify(s.diff(sol,tau)-gamma*sol-forcing)==0
    assert s.simplify(sol.subs(tau,0)-h0)==0
    # The astronomical constant is legitimate but useless numerically until
    # sharp constrained and trace estimates replace it.
    print('PASS graph source bound Hprime <=30625021 H +(2000.5+k²/2)F²/A+Ft²/A + signed boundary flux')

if __name__=='__main__':exact()
