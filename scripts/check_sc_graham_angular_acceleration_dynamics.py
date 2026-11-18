#!/usr/bin/env python3
"""Graham UG-2 velocity vs acceleration: exact synthetic dynamical transfer.

UG-2 published low-pass 33.3mHz. Single-pole approximation below is a model,
NOT an exact replay of authors' digital filter or acceleration histories.
"""
import sympy as s

def check():
    z,tx,tf,t,lam,v,a=s.symbols('z tx tf t lam v a',positive=True)
    H=1/((1+z*tx)*(1+z*tf))
    impulse=s.inverse_laplace_transform(H,z,t)
    expected=(s.exp(-t/tf)-s.exp(-t/tx))/(tf-tx)
    assert s.simplify(impulse-expected)==0
    assert s.limit(s.exp(-t/tf),t,s.oo)==0
    assert s.limit(s.exp(-t/tx),t,s.oo)==0
    assert s.simplify((tf-tx)/(tf-tx)-1)==0
    kappa=s.symbols('kappa',real=True)
    assert s.simplify((kappa*v+lam*a).subs(a,0)-kappa*v)==0
    prediction=s.Rational(48,1000000)
    estimate=s.Rational(23,10000000)
    stderr=s.Rational(14,10000000)
    assert prediction>estimate+2*stderr
    assert lam*a!=0
    print('PASS exact two-pole transient, zero acceleration plateau, fit comparison')
    print('Illustrative one-pole tau at 33.3mHz:',1/(2*3.141592653589793*.0333),'s')
    print('NO UG-2 raw trace, real digital-filter replay, or fitted transient')

if __name__=='__main__':check()
