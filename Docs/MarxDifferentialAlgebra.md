# Marx differential algebra in DASHI

## Implemented spine

The formal sequence is explicit:

```text
original function
  -> finite transport
  -> preliminary derived function
  -> factorisation receipt
  -> lawful diagonal collapse
  -> final derived function
```

For a selected algebra `A`, a factorisation receipt contains a two-point preliminary function `F` and the equation

```text
f(x1) - f(x) = (x1 - x) * F(x,x1).
```

The Marx derivative is definitionally

```text
D_M f(x) = F(x,x).
```

No quotient is evaluated on the diagonal. `RawDiagonalQuotient` requires a proof that `x - x` is nonzero, and `rawDiagonalQuotientImpossible` contradicts it using `subSelf`.

## Exact algebraic results

`MarxDifferentialCore` constructs:

- constant factorisation and `D_M(c)=0`;
- identity factorisation and `D_M(x)=1`;
- closure under addition and multiplication;
- sum and product rules;
- composition from nested finite transports;
- the exact chain rule;
- quotient factorisation as multiplication by a receipted reciprocal.

## Constructive-real completion path

`MarxConstructiveRealAdapter` identifies the selected `ConstructedOrderedCompleteReal` as the intended carrier.

`MarxConstructiveRealRingNormalisation` now derives the two finite-difference factor laws from a small explicit quotient-level ring-normalisation package:

```text
x * 0 = 0
subtraction as addition of a negative
difference of sums
difference of products
0 != 1
1 + 1 != 0
```

It constructs:

- `constructedRealRingNormalisation`;
- `ordinaryConstructiveRealMarxAlgebra`;
- `ordinaryConstructiveRealMarxPackage`;
- `ordinaryMarxCarrierNonterminal`.

`MarxFastCauchyCompletionCutset` binds this directly to the existing repository stack:

```text
FastCauchyOperations
  -> SetQuotientBackend
  -> FastCauchyQuotientOperations
  -> FastCauchyQuotientAlgebraLaws
  -> FastCauchyQuotientCompleteness
  -> ConstructedOrderedCompleteReal
  -> MarxAlgebra.
```

The existing representative-respect theorems for addition, subtraction, multiplication, and negation are reused. The remaining nondegenerate real leaf is therefore not a new real-number design: it is a concrete quotient backend plus quotient-level ring normalisation and nondegeneracy.

## Power and polynomial regime

`MarxPowerRuleNormalisation` defines the natural scalar internally:

```text
[n]_A = 1 + ... + 1
n . x = [n]_A * x
```

It proves:

- `natCastZero` and `natCastSuccessor`;
- `natScaleZero`, `natScaleOne`, and `natScaleSuccessor`;
- natural scaling through multiplication;
- the inductive theorem

```text
D_M(x^(n+1)) = (n+1) . x^n.
```

The selected constructed real inherits the normalization through `ordinaryRealPowerRuleNormalisation` once its ring-normalisation package is supplied.

The polynomial layer now also contains a structurally differentiated polynomial syntax and proves that its interpretation agrees with the existing receipt-derived polynomial derivative.

## Reciprocal and quotient regime

`MarxReciprocalQuotientNormalisation` defines an explicit field-level cutset:

- `Nonzero`;
- reciprocal and reciprocal nonzero transport;
- left/right inverse laws;
- the finite reciprocal-difference identity;
- reciprocal finite factorisation;
- reciprocal derivative;
- reciprocal denominator-square normalization;
- quotient construction through the existing product rule;
- quotient product form;
- the standard denominator-squared quotient rule;
- `LocallyNonzeroAt` for punctured-neighbourhood domain control.

The printed theorem is now obtained through the existing product factorisation:

```text
D_M(f/g)
  = (g * D_M f - f * D_M g) * reciprocal(g*g).
```

No unrelated direct quotient derivative is postulated.

## Ordinary derivative bridge

The former weak remainder and placeholder diagonal surfaces have been replaced.

`RemainderDerivativeStructure` now owns punctured normalization and convergence. An ordinary derivative carries

```text
f(x+h) = f(x) + L*h + r(h)
```

with the actual little-o condition

```text
normaliseRemainder(h,r(h)) -> 0
```

on nonzero `h`.

`PreliminaryContinuousAtDiagonal` is the genuine convergence statement

```text
F(x,x+h) - F(x,x) -> 0.
```

The module defines

```text
r_M(h) = h * (F(x,x+h) - F(x,x))
```

and proves

```text
Marx factorisation
+ diagonal continuity
+ finite rearrangement laws
-> ordinary remainder derivative with coefficient D_M f(x).
```

Derivative uniqueness then yields `marxDerivativeEqualsOrdinaryDerivative`. The compatibility authority no longer contains the desired equality as an assumption; it carries only the finite rearrangement and uniqueness laws from which the equality is derived.

A converse divided-difference-extension constructor is also present.

## Fréchet calculus and Jacobians

`MarxHigherCalculus` now uses genuine structures rather than one-field placeholders:

- modules with vector addition and scalar action;
- linear maps preserving zero, addition, and scaling;
- identity, zero, and composition of linear maps;
- ordered scalar carriers;
- normed modules;
- bounded linear maps and operator-norm receipts;
- vector-valued little-o structures;
- Fréchet derivatives with linear derivative, explicit remainder, and little-o proof;
- identity and constant Fréchet derivatives;
- additive and chain-rule construction data;
- derivative uniqueness;
- directional derivatives as applications of the Fréchet derivative;
- finite bases, coordinate functionals, and Jacobian extraction.

The repository's checked Jacobian counterexample is imported as a promotion boundary:

```text
constant or nonsingular Jacobian data
  does not entail global injectivity.
```

Local differential information, local inversion, finite fibres, global injectivity, and global polynomial invertibility remain distinct strata.

## Differential forms and integration

`MarxExteriorIntegration` adds:

- degree-indexed alternating multilinear maps;
- graded differential-form carriers;
- wedge-product interfaces;
- an exterior derivative with the genuine target

```text
d (d omega) = zeroForm;
```

- a concrete zero-differential regression inhabitant;
- literal intervals, tagged cells, tagged partitions, and finite Riemann sums;
- constructive integral laws for constants, sums, scaling, order, and interval additivity;
- equality-valued fundamental-theorem interfaces;
- a cumulative-harm integral surface.

The previous tautology `d(d omega)=d(d omega)` has been removed.

## Social recursion differential

`TraumaExploitationDifferential` differentiates the heterogeneous recursion

```text
HistoricalState
  -> SufferingField
  -> ExploitationProtocol
  -> Institution
  -> HistoricalState
```

as

```text
dReproduce
  o dInstitutionalise
  o dExploitationExtraction
  o dTraumaProduction.
```

`DifferentialAttribution` keeps distinct:

- where suffering enters;
- where it becomes an extraction protocol;
- where it becomes institutionally scalable;
- where it is reproduced or externalised.

The promotion boundary has been strengthened. Every normative authority must carry independent evidence, and a gain-only authority attempt is contradictory.

## Evidence-bound geopolitical layer

`GeopoliticalDifferentialEvidence` defines:

- claim, jurisdiction, time, population, sector, and technology scope;
- source receipts and source roles;
- independent evidence;
- legal procedural stages;
- the indexed theorem that provisional measures or a pending counter-memorial do not constitute a final merits judgment;
- cyber/economic evidence with explicit units and methodology;
- explicit global-player criteria;
- product, buyer, capability, use, and affected-population deployment receipts;
- doctrine-to-technology-to-institution-to-externalisation mechanism receipts;
- PNF support, contradiction, alternatives, and missing-axis fibres;
- a full promotion receipt requiring source completeness, scope/time alignment, mechanism evidence, counterevidence, legal precision, non-essentialisation, and independent evidence;
- an impossibility theorem for gain-only promotion.

`IsraelCyberLegalStatusCandidate` is a deliberately narrow, fail-closed fixture. It records current official aggregate high-tech/defence-export evidence and current ICJ procedural status, but leaves the trauma-to-cyber-export mechanism undetermined because cyber-only denominators, product deployment, buyer/use, and causal mechanism receipts are absent. The fixture cannot promote that mechanism.

## Regression and CI

`MarxDifferentialRegression` now exercises:

- constants, identity, sums, products, composition, and diagonal non-collapse;
- law-derived natural-scalar power normalization;
- polynomial differentiation;
- reciprocal and quotient constructions;
- the little-o compatibility theorem;
- module and Fréchet identity structure;
- directional differentiation;
- the genuine `d^2=0` target;
- Riemann integration structure;
- legal procedural non-collapse.

The focused workflow typechecks the complete `MarxDifferentialBundle` and watches every new dependency, including the Jacobian kernel boundary.

## Files

- `DASHI/Analysis/MarxDifferentialCore.agda`
- `DASHI/Analysis/MarxPolynomialDifferential.agda`
- `DASHI/Analysis/MarxConstructiveRealAdapter.agda`
- `DASHI/Analysis/MarxConstructiveRealRingNormalisation.agda`
- `DASHI/Analysis/MarxFastCauchyCompletionCutset.agda`
- `DASHI/Analysis/MarxPowerRuleNormalisation.agda`
- `DASHI/Analysis/MarxReciprocalQuotientNormalisation.agda`
- `DASHI/Analysis/MarxOrdinaryDerivativeBridge.agda`
- `DASHI/Analysis/MarxHigherCalculus.agda`
- `DASHI/Analysis/MarxExteriorIntegration.agda`
- `DASHI/Analysis/MarxDifferentialRegression.agda`
- `DASHI/Analysis/MarxDifferentialBundle.agda`
- `DASHI/Governance/TraumaExploitationDifferential.agda`
- `DASHI/Governance/GeopoliticalDifferentialEvidence.agda`
- `DASHI/Governance/IsraelCyberLegalStatusCandidate.agda`

## Honest remaining substantive inhabitants

The requested theorem architecture and dependency reductions are now present. The remaining work is concrete rather than architectural:

1. inhabit the repository's backend-neutral `SetQuotientBackend` for fast-Cauchy reals;
2. prove quotient-level subtraction/negation normal forms and nondegeneracy for that backend;
3. inhabit the ordinary-real reciprocal laws and denominator-square normalization;
4. bind the selected real order/absolute value to punctured little-o convergence and prove derivative uniqueness;
5. construct nonterminal normed finite-dimensional modules, operator norms, exterior forms, and Riemann/Fundamental-Theorem inhabitants;
6. populate product-level deployment and mechanism evidence for any concrete geopolitical promotion.

No missing backend, real-analysis theorem, or empirical causal link is fabricated merely to make a status flag green.
