#!/usr/bin/env python3
"""Angular lattice-drive -> coherent condensate lag transfer and passivity.

Conditional coarse-grained angular mode. psi is relative MECHANICAL phase
displacement (radians), NOT an identified microscopic BCS condensate phase.
K, eta, Is require TDGL/BCS-vortex derivation and are not fitted here.
Source attribution: existing Filsinger signed work; rotating TDGL literature.
"""
import sympy as s

def main():
    z, Is, K, eta=s.symbols('z I_s K eta',positive=True)
    Hs=(K+eta*z)/(Is*z*z+eta*z+K)
    Hl=s.factor(1-Hs)
    assert s.simplify(Hl-Is*z*z/(Is*z*z+eta*z+K))==0
    assert s.simplify(Hs.subs(z,0)-1)==0
    assert s.simplify(Hl.subs(z,0))==0
    assert s.limit(Hs,z,s.oo)==0
    assert s.limit(Hl,z,s.oo)==1
    a=s.symbols('a',real=True)
    lag_laplace=-a*Hl/z**2
    assert s.simplify(s.limit(z*lag_laplace,z,0))==0
    K0=s.simplify(lag_laplace.subs(K,0))
    assert s.simplify(s.limit(z*K0,z,0)+Is*a/eta)==0
    psi_laplace=Hl*(-a/z**2)/z
    assert s.simplify(s.limit(z*psi_laplace,z,0)+Is*a/K)==0
    w=s.symbols('w',positive=True)
    den=Is*(s.I*w)**2+eta*(s.I*w)+K
    assert s.simplify(s.expand_complex(den*s.conjugate(den))-
        ((K-Is*w**2)**2+eta**2*w**2))==0
    print('PASS exact transfer, finite stiffness versus zero stiffness, phase-offset under steady acceleration')
    print('H_condensate(z)=',Hs)
    print('H_lattice-minus-condensate(z)=',Hl)
    print('natural frequency sqrt(K/I_s); damping eta/I_s')
    print('OPEN microscopic Josephson/flux pinning stiffness, vortex damping and measured response')
if __name__=='__main__':main()
