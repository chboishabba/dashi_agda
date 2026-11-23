#!/usr/bin/env python3
"""Attribution-bounded YBCO rotor and entangled sensor MCG QFI model.

Source attribution:
* G. Hathaway, B. Cleveland, Y. Bao, Physica C 385 (2003) 488-500:
  1300 rpm fracture/0.5MPa, typical 400rpm, actual maximum ~550rpm,
  RF drag and failed AC levitation; their extrapolation is not verified.
* E. Podkletnov, later 1997 manuscript: claimed ~5000rpm operation,
  not independently reproduced here.
* 2026 Nature Communications distributed superconducting 4-qubit GHZ
  vector-gradient demonstration and 2025 experimental noisy distributed
  quantum sensing: small laboratory demonstrations, not entangled MCG.
Original SymPy derivation: Markovian QFI/time budget, common-noise penalty.
"""
import sympy as s

def verify():
    N,t,g,gc=s.symbols('N t gamma gamma_c',positive=True)
    rpm=s.symbols('rpm',positive=True)
    stress=s.Rational(1,2)*(rpm/s.Integer(1300))**2 # MPa conditional
    assert stress.subs(rpm,1300)==s.Rational(1,2)
    assert stress.subs(rpm,5000)==s.Rational(1250,169)
    assert s.simplify(stress.subs(rpm,5000)/stress.subs(rpm,1300)-
                      s.Rational(2500,169))==0
    assert (s.Integer(5000)/550)**4>6000
    print('Conditional rotor stress MPa at 550,1300,2000,5000 rpm:',
          *[float(stress.subs(rpm,x)) for x in (550,1300,2000,5000)])

    # Parameter generator H=b/2 sum_i sigma_z. Normalized fixed-time QFI.
    # Visibility: independent exp(-N gamma t), common exp(-N^2 gamma_c t).
    qprod=N*t**2*s.exp(-2*g*t)
    qghz=N**2*t**2*s.exp(-2*(N*g+N**2*gc)*t)
    assert s.simplify(qghz.subs({g:0,gc:0})/qprod.subs(g,0)-N)==0
    # Fixed total laboratory time: maximize QFI/t to account for restarts.
    prod_rate=qprod/t
    ghz_rate=qghz.subs(gc,0)/t
    tp=1/(2*g)
    tg=1/(2*N*g)
    assert s.simplify(s.diff(prod_rate,t).subs(t,tp))==0
    assert s.simplify(s.diff(ghz_rate,t).subs(t,tg))==0
    assert s.simplify(prod_rate.subs(t,tp)-ghz_rate.subs(t,tg))==0
    tc=1/(2*(N*g+N**2*gc))
    assert s.simplify(s.diff(qghz/t,t).subs(t,tc))==0
    ratio=s.simplify(((qghz/t).subs(t,tc))/prod_rate.subs(t,tp))
    assert s.simplify(ratio-g/(g+N*gc))==0
    # A GHZ state can erase an anti-correlated signal if weights are wrong.
    a,b=s.symbols('a b',real=True)
    qcommon=(a+b)**2*t**2
    qgradient=(a-b)**2*t**2
    assert s.simplify(qcommon.subs(b,-a))==0
    assert s.simplify(qgradient.subs(b,-a)-4*a*a*t*t)==0
    print('Noiseless same-time GHZ / independent QFI: N')
    print('Independent Markov dephasing optimum QFI per total time ratio: 1')
    print('Common-dephasing optimal information-rate ratio:',ratio)
    print('N=1000 ideal fixed-time amplitude advantage:',s.sqrt(1000).evalf(8))
    assert s.sqrt(1000)<1076
    print('PASS exact stress scaling and quantum Fisher information controls')
    print('NOT tested: source magnetic field, entanglement distribution, SOTA MCG')

if __name__=='__main__':verify()
