#!/usr/bin/env python3
"""Exact finite-array diamond MCG detection identities, not clinical evidence.

Prior-art consumers: DiamondMCGFiniteBridgeExact (forward mode),
psychotronics_field_loom_covariance.py (shared-error GLS), and
NVSIMetrologyReadoutAdapterExact (SI/calibration boundary).
Original measurement attribution: Omar et al., Sci Adv 2026 eaeg5281.
"""
import sympy as s


def check(name, expression):
    residual = expression.applyfunc(s.factor) if isinstance(expression, s.MatrixBase) else s.factor(expression)
    if residual != (s.zeros(*residual.shape) if isinstance(residual, s.MatrixBase) else 0):
        raise AssertionError(f'{name}: {residual}')
    print('PASS', name)


def main():
    a,b,c,sigma=s.symbols('a b c sigma', positive=True)
    # N-channel equicorrelated SPD family, 0 <= c < 1.
    for n in (1,2,3,5,10):
        I=s.eye(n); one=s.ones(n,1)
        C=sigma**2*((1-c)*I+c*one*one.T)
        inv_formula=(I-c*one*one.T/(1+(n-1)*c))/(sigma**2*(1-c))
        check(f'inverse-{n}',s.simplify(C*inv_formula-I)) if n==1 else None
        if n>1:
            for i in range(n):
                for j in range(n):
                    check(f'inverse-{n}-{i}-{j}',s.cancel((C*inv_formula-I)[i,j]))
        response=a*one
        info=s.cancel((response.T*inv_formula*response)[0])
        check(f'effective-N-{n}',info-a*a*n/(sigma*sigma*(1+(n-1)*c)))
        weights=inv_formula*response
        check(f'optimal-direction-{n}',s.cancel(weights[0]-a/(sigma*sigma*(1+(n-1)*c))))
    # Nulling common-mode contamination also removes target common-mode power.
    x,y=s.symbols('x y',real=True)
    target=s.Matrix([x,y]); u=s.Matrix([1,1]); P=s.eye(2)-u*u.T/2
    check('common-mode-null',P*u)
    check('differential-target-power',s.expand((P*target).dot(P*target)-(x-y)**2/2))
    check('uniform-target-lost',P*s.Matrix([a,a]))
    # Known-response matched filter for a general 2-channel SPD covariance.
    v,w,k=s.symbols('v w k',positive=True)
    C2=s.Matrix([[v,k],[k,w]])
    signal=s.Matrix([x,y]); inv=C2.inv()
    matched=inv*signal
    info=s.factor((signal.T*matched)[0])
    check('two-channel-schur-information',info-(w*x*x-2*k*x*y+v*y*y)/(v*w-k*k))
    r,r0,A,S,z,T=s.symbols('r r0 A S z T',positive=True)
    amp=A*(r0/r)**3
    Tmin=s.factor((z*S/amp)**2)
    check('coherent-sixth-power',Tmin-(z*S/A)**2*(r/r0)**6)
    # Independent noncoherent blocks of fixed duration tau.
    tau=s.symbols('tau',positive=True)
    Tnon=s.factor((z*S/amp)**4/tau)
    check('noncoherent-twelfth-power',Tnon-(z*S/A)**4*(r/r0)**12/tau)
    print('All exact symbolic identities passed; physical calibration, detection probabilities, PSD and source attribution remain OPEN.')


if __name__=='__main__':main()
