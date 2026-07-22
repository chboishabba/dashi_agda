# Elementary single-operator extended formalism

## Scope

This tranche extends the structural EML compiler merged in PR #312 without
promoting branch-sensitive scalar analysis or the constant-free ternary candidate
beyond what has actually been proved.

## Binary EML

`DASHI.Foundations.EMLAnalyticDomain` separates total evaluation from analytic
definedness.  `DefinedSource` and `DefinedEML` track whether every source or EML
node is legitimate on the selected domain.  `EMLCompilerDefinedness` is the exact
closure obligation introduced by the compiler.

`EMLPositiveRealAnalyticPackage` fixes the carrier to DASHI's canonical real
authority and packages the required positive-domain exp/log laws.
`EMLComplexBranchPackage` makes the logarithm branch, branch domain, principal
strip, and compiler-intermediate closure explicit.

`EMLConcreteSmokeModel` is a concrete degenerate model used only to exercise the
compiler in CI.  It does not promote real or complex calculator semantics.

## Scientific calculator front end

`DASHI.Foundations.ElementaryCalculator` defines the full 36-primitive surface
used by arXiv:2603.21852v2:

- constants and variables;
- exp, log, reciprocal, half, negation, square root, square, sigmoid;
- trigonometric, inverse-trigonometric, hyperbolic, and inverse-hyperbolic
  functions;
- addition, subtraction, multiplication, division, arbitrary-base logarithm,
  power, average, and hypotenuse;
- signed integer and rational literals.

Every constructor lowers to the `1/exp/log/sub` kernel and then through the
single-node EML compiler.  `CalculatorMeaning` is the independent semantic
obligation: syntactic lowering alone does not establish global complex identities.

## Constant-free ternary candidate

`TernaryWitnessIndependentRepresentation` proves that diagonal unit generation
yields a reusable, witness-independent semantic unit whenever the diagonal law
holds.  It also proves the structural reduction:

> unit tree + variable trees + one correct EML context imply a complete
> `TernaryRepresentsEML` translation.

The missing research theorem is therefore concentrated in the construction and
analytic correctness of those contexts for the proposed ternary operator.

`TernaryElementarySearchCertificate` defines bounded-tree complexity,
candidate status, side-condition-aware exp/log rewrite certificates, exact
promotion records, and counterexample boundaries.  The Python search script is
strictly scout-only and cannot produce a promoted theorem.

## Related formal boundaries

- `SpectralCountingComplexity` separates discrete/cuspidal, continuous/scattering,
  principal Weyl, and remainder terms before deriving an MDL budget.
- `DissipationNullComputationalCarrier` records that harmonic/nullspace carriers
  can remain computationally nontrivial while viscosity vanishes.
- `DivergenceComparisonPackage` assigns squared Hellinger, TV, KL, and JS to
  distinct typed roles and rejects a universal strict winner.
- `BraKet` adds explicit bra/ket wrappers over the existing inner-product
  interface.
- `TernaryCircuit` and `FiniteTernaryQuantumCircuitAdapter` add a finite reversible
  qutrit permutation circuit while keeping amplitudes, arbitrary unitaries, and
  full quantum algorithms unpromoted.

## Promotion boundary

Machine checking of the new structural modules does not by itself provide:

1. a constructed real-number exponential/logarithm implementation;
2. a globally valid principal-complex-log compiler;
3. an analytic proof of every calculator identity on one common domain;
4. ternary functional completeness;
5. a full qutrit quantum computer;
6. automorphic Weyl authority or time-dependent Navier-Stokes universality.
