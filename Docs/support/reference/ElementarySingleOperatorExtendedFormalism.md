# Elementary single-operator extended formalism

## Scope

This tranche extends the structural EML compiler merged in PR #312 without
promoting branch-sensitive scalar analysis or the constant-free ternary candidate
beyond what has actually been proved. The focused workflow
`elementary-single-operator-extended.yml` checks every module listed below and
runs the fail-closed scout/audit lane.

## Binary EML

`DASHI.Foundations.EMLAnalyticDomain` separates total evaluation from analytic
definedness. `DefinedSource` and `DefinedEML` track whether every source or EML
node is legitimate on the selected domain. The central safety object is now
expression-indexed:

- `CompilationDefined M D rho t` recursively proves source definedness;
- each constructor also proves that the exact compiled EML node, including all
  compiler-introduced logarithm arguments, is defined;
- `analyticCompileCorrect` proves compiler correctness only from that certificate.

`EMLCompilerDefinedness` remains available as the stronger convenience interface
for globally closed/total models; it is not required of branch-sensitive models.

`EMLPositiveRealAnalyticPackage` fixes the carrier to DASHI's canonical real
authority and identifies log admissibility with a supplied positivity predicate.
`EMLComplexBranchPackage` makes the logarithm branch, branch domain, principal
strip, and sign convention for the derived imaginary unit explicit. Their semantic
laws are required only for certified compiled expressions, not globally across a
branch cut.

`EMLConcreteSmokeModel` is a concrete degenerate model used only to exercise the
compiler in CI. It does not promote real or complex calculator semantics.

## Scientific calculator front end

`DASHI.Foundations.ElementaryCalculator` defines the complete calculator surface
used by arXiv:2603.21852v2:

- constants and variables;
- exp, log, reciprocal, half, negation, square root, square, sigmoid;
- trigonometric, inverse-trigonometric, hyperbolic, and inverse-hyperbolic
  functions;
- addition, subtraction, multiplication, division, arbitrary-base logarithm,
  power, average, and hypotenuse;
- signed integer and rational literals.

Every constructor lowers to the `1/exp/log/sub` kernel and then through the
single-node EML compiler.

`ElementaryCalculatorSemantics` defines an independent named calculator semantic
model, exact primitive-law record, and the structural lowering theorem for every
constructor. `ElementaryCalculatorAnalyticPackage` combines:

- branch/domain-sensitive EML laws;
- an independent calculator semantic model;
- all primitive lowering laws;
- an expression-domain predicate;
- an expression-indexed `CompilationDefined` certificate;
- compiled definedness and final semantic correctness.

`ElementaryCalculatorSmokeModel` gives a concrete singleton regression receipt for
all constructors without claiming analytic authority.

## Constant-free ternary candidate

`TernaryWitnessIndependentRepresentation` proves that diagonal unit generation
yields a reusable, witness-independent semantic unit whenever the diagonal law
holds. It also proves the structural reduction:

> unit tree + variable trees + one correct EML context imply a complete
> `TernaryRepresentsEML` translation.

`TernaryCalculatorUniversality` composes any future `TernaryRepresentsEML` witness
with the complete calculator compiler. Thus one actual ternary EML representation
would immediately yield a constant-free ternary calculator translation on the
selected analytic domain. `TernaryCalculatorSmokeModel` exercises that composition
on a deliberately degenerate singleton model only.

The unresolved research theorem is the construction or refutation of the required
EML context for the proposed analytic ternary operator.

## Search and certification

`TernaryElementaryBoundedEnumeration` gives a literal finite enumeration of
ternary trees by variable set and depth. Structural and semantic deduplication are
kept as separately certified passes.

`TernaryElementarySearchCertificate` defines:

- node/depth/variable accounting;
- target and candidate statuses;
- a symbolic exp/log/sub/mul/div language;
- branch, strip, and nonzero side conditions;
- exact rewrite traces;
- certified-candidate and counterexample records.

`TernaryElementarySearchSoundness` proves every rewrite trace semantically sound
relative to an explicit operation model and proofs for each side-conditioned
rewrite. `TernaryElementarySearchSmokeModel` checks this induction concretely.

`scripts/search_ternary_elementary_candidates.py` performs a bounded numerical
beam search for `1`, `exp`, `log`, subtraction, and EML. Its output remains
`scoutOnly`; numerical agreement cannot inhabit an Agda certificate.

## Related formal boundaries

- `SpectralCountingComplexity` separates discrete/cuspidal, continuous/scattering,
  principal Weyl, and remainder terms before deriving an MDL budget.
- `DissipationNullComputationalCarrier` records that harmonic/nullspace carriers
  can remain computationally nontrivial while viscosity vanishes.
- `DivergenceComparisonPackage` assigns squared Hellinger, TV, KL, and JS to
  distinct typed roles and proves only conditional comparison transfers.
- `BraKet` adds explicit bra/ket wrappers and an involutive dagger interface over
  the existing inner-product carrier.
- `TernaryCircuit` supplies reversible one-qutrit cycles, reversible two-qutrit
  controlled-cycle/SUM and swap gates, circuit composition, and inverse proofs.
- `QutritUnitaryBridge` turns the cycle permutation into the existing abstract
  `Unitary` interface once a qutrit inner-product preservation authority is given.
- `FiniteTernaryQuantumCircuitAdapter` records the finite reversible basis layer
  while keeping amplitudes, arbitrary unitary matrices, algorithms, and a full
  qutrit quantum computer explicitly unpromoted.

## Promotion boundary

Machine checking of the new structural modules does not by itself provide:

1. a constructed real-number exponential/logarithm implementation;
2. a globally valid principal-complex-log compiler;
3. an inhabited analytic calculator package over a standard real/complex model;
4. ternary functional completeness or an impossibility theorem;
5. amplitude-level qutrit superposition or a full quantum computer;
6. automorphic Weyl authority or time-dependent Navier-Stokes universality.
