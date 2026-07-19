# DASHI Shor / RSA / quantum-computation join

## Status

This lane formalises the finite algorithmic seam between the existing DASHI
quantum-computation programme and RSA arithmetic. It is intentionally split
into constructive finite certificates and fail-closed quantum probability
interfaces.

Implemented:

- finite computational registers and reversible circuits;
- a finite quantum Fourier transform interface, distinct from the repository's
  `QFTParitySurface` (quantum field theory);
- general finite abelian hidden-subgroup and cyclic hidden-period problems;
- Shor period-finding machines with explicit successful-sample evidence;
- modular order-finding as a hidden-period specialization;
- general Shor factoring and discrete-logarithm surfaces;
- exact factor certificates carrying cofactors and multiplication equalities;
- RSA public-modulus vulnerability and quantum-break bridges;
- concrete checked arithmetic witnesses for `N = 15, a = 2, r = 4` and
  `N = 21, a = 2, r = 6`;
- an executable deterministic arithmetic audit and focused CI.

## Productive join

```text
RSAArithmeticCore.powMod
        |
        v
ExactOrderCertificate / ModularOrderProblem
        |
        v
HiddenPeriodProblem
        |
        v
FiniteQuantumRegister + FiniteFourierTransform
        |
        v
ShorPeriodFindingMachine
        |
        v
CertifiedShorSplit
        |
        v
FactorCertificate
        |
        v
RSAShorVulnerability
```

`DASHIShorProductiveJoin` packages the existing
`QuantumComputationProgramme`, a general period-finding machine, and an RSA
vulnerability witness. The existing hybrid semantic step retains its proved
code-length nonincrease theorem.

## Proof boundary

Constructive in this lane:

- factor/cofactor multiplication equalities;
- period equalities supplied by finite `powMod` computation;
- even-order decomposition;
- exact branch witnesses for `a^(r/2) - 1` or `a^(r/2) + 1`;
- extraction of a nontrivial factor certificate;
- concrete 15 and 21 examples;
- executable finite order and gcd auditing.

Still explicit inputs or evidence records:

- the full modular exponent transport law
  `a^(x+r) mod N = a^x mod N` derived from modular algebra;
- exact-period minimality for arbitrary inputs;
- construction of physical finite-register amplitudes;
- QFT sampling-distribution and continued-fraction probability bounds;
- a physical quantum-computer implementation.

No quantum speedup, physical device, or universal RSA break is promoted merely
from the existence of the interfaces.

## Files

- `DASHI/Algebra/Quantum/FiniteQuantumRegister.agda`
- `DASHI/Algebra/Quantum/QuantumFourierTransformFinite.agda`
- `DASHI/Algebra/Quantum/GeneralShor.agda`
- `DASHI/Crypto/FiniteFactorArithmetic.agda`
- `DASHI/Crypto/ShorOrderFinding.agda`
- `DASHI/Crypto/ShorFactoring.agda`
- `DASHI/Crypto/ShorDiscreteLog.agda`
- `DASHI/Crypto/RSAShorVulnerabilityBridge.agda`
- `DASHI/Crypto/ShorConcreteExamples.agda`
- `DASHI/Algebra/Quantum/DASHIShorProductiveJoin.agda`
- `DASHI/Crypto/ShorProgram.agda`
- `scripts/shor_order_finding_audit.py`

## Audit

```bash
python -m pytest -q scripts/tests/test_shor_order_finding_audit.py
python scripts/shor_order_finding_audit.py --pretty
```
