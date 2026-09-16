# Yang–Mills CMP Work Status

Status: navigation / archaeology companion to `YMRHPRRoundArchaeologyAudit.md`. **Not theorem authority and not a Clay-completion claim.**

Purpose: stop repeated proof-search from treating `CMP99`, `CMP102`, `CMP109`, `CMP116`, `CMP119`, or `CMP122` as one undifferentiated open task. Reopen a CMP-labelled object only when a current consumer exposes a specific unpaid same-object physical/source instantiation.

## Executive rule

**DO NOT reopen “formalise CMP109/116/119/122” as a generic task.**

| Source family | Repository status for current search | Already owned | Legitimately open only when demanded |
|---|---|---|---|
| CMP99 | SOURCE PROPAGATOR AUTHORITY OWNED | regular-background Green/gradient bounds, analytic background dependence, marked domain-sequence propagator comparison | exact attachment to a selected consumer if the optional perturbative producer is used |
| CMP102 | SOURCE VARIATIONAL/BACKGROUND AUTHORITY OWNED | background criticality/minimization/uniqueness modulo gauge, analyticity/locality/derivative locality, common source radius | exact `C` identification only for the optional R367 cross-parameter route |
| CMP109 | SOURCE/COMPILER LARGELY OWNED | regular small-field effective-action lane, differentiated coordinates, R103 polarization/Hessian same-carrier identity, Eq.(5.1)-facing continuation | one literal physical differential/source identification demanded by a live consumer |
| CMP116 | SOURCE/COMPILER LARGELY OWNED | fixed-point ball preservation/contraction, analytic fixed-point dependence, marked/localized differentiated activity machinery, common source domain/radius framework | selected same-object family/domain/radius/distance attachments and consumer-specific quantitative calibration |
| CMP119 | SOURCE OBJECT/DICTIONARY LARGELY OWNED | complete-density dictionary, finite-beta construction, raw source state, function-valued regular `E_k`, selected regular-E projection | exact selected physical realization only when demanded downstream |
| CMP122 | PUBLISHED THEOREM BOUNDARY OWNED | Theorem-1/UV-stability authority, finite-history coupling hypothesis, active-scale source carrier | exact selected-family instantiation; continuum/OS/mass-gap remain separate |

## Current live sensitivity recut: R368--R386

The preferred direct route is no longer the old cross-propagator / CMP102-Lipschitz construction and no longer requires a historical marked-input calibration for the Hessian-coefficient consumer.

### R368 — fixed-parameter contraction is source-shaped directly

`BalabanCMP116DirectDecoupledContractionRound368Exact.agda` uses the literal composite map

```text
F_s(X) = C(A' - H(s)X)
```

on its source ball. A CMP102→CMP116 C identity is not mandatory merely to recover same-parameter contraction.

### R370/R371 — direct fixed-point parametric sensitivity

`BalabanCMP116DirectParametricSensitivityRound370Exact.agda` provides the generic Cauchy/mean-value ABI. Once the selected CMP116 analytic fixed-point family, common neighbourhood, uniform magnitude/radius and parameter-distance upper are attached, it proves

```text
d_boundary^R370(s) <= U_par
U_par := L_par(M,r) * d_parameter.
```

`BalabanCMP116PublishedParametricFixedPointRound371Exact.agda` records the corresponding CMP116 Sect.1 source theorem shape. The older R365--R369 perturbative route remains optional.

### R372/R373 — same Cauchy mechanism for the local Hessian

R372 reuses the same parametric-sensitivity ABI for the selected local Hessian family. R373 attaches that theorem to the literal boundary Hessian scalar. No independent primitive `D^3` / Hessian-Lipschitz theorem is mandatory.

### R374/R375 — common radius and existing coefficient lift

R374 reuses one canonical CMP116 radius for both fixed-point and Hessian derivative consumers.

R375 sends R372/R373 pointwise Hessian sensitivity into the already-owned `BalabanDecoupledActivityHessian.markedSubstitutionStabilityLiftsToCoefficient` theorem. R103 already owns the literal CMP116 marked-Hessian = CMP109 polarization = D² effective-potential carrier identity.

### R376/R377/R378 — historical-mark compatibility route

R376 splices the old R351 H_sub carrier into R375.

R377 removes duplicated selected distance coordinates: the R351 selected distance is defined to be the R373 boundary distance; only the boundary-to-source distance attachment remains proof-bearing.

R378 factors the R351 source inequality through R370:

```text
d_boundary <= U_par
U_par <= M_marked^src
--------------------
d_boundary <= M_marked^src.
```

This is a valid compatibility producer when a downstream consumer truly needs the historical/source marked coordinate.

### R379 — consumer audit removes the historical-mark overpayment

`BalabanCMP116DistanceUpperHessianBidiRound379Exact.agda` checks what R375 actually observes. The coefficient theorem only needs

```text
0 <= U
selectedBoundarySubstitutionDistance(s) <= U.
```

It does not inspect the provenance/identity of `U` as a historical mark. Therefore `U` is recut to the least-privilege `distanceUpper` coordinate.

### R380 — first direct R370→R379 compatibility composition

R380 chooses `U := U_par`. It remains a valid compatibility bridge, but subsequent rounds remove its duplicated selected-boundary coordinates from the preferred path.

### R381 — R373 selected distance is literally the R370 boundary distance

`BalabanCMP116CanonicalR370R373BoundaryRound381Exact.agda` chooses the R373 boundary carrier to be the R370 boundary carrier and defines the selected distance to be `R370.boundarySubstitutionDistance`. The R380 boundary map and selected-distance equality become `refl`.

WrongType correction: the fixed-point Lipschitz constant and Hessian-family Lipschitz constant are **not** identified. R373's selected Lipschitz is the R372 Hessian Lipschitz.

### R382/R383 — useful compatibility specializations

R382 measures Hessian Cauchy sensitivity in the exact R370 fixed-point-output metric, eliminating a second R372↔R370 distance weld. R383 specializes the generic Hessian family to the already-owned literal R103 `cmp116PhysicalMarkedHessian` and chooses the R373 boundary scalar as the difference coordinate by construction.

These remain useful compatibility reductions, but R384/R385 expose an even smaller acyclic route.

### R384 — remove the legacy H_local socket from the fixed-point distance producer

`BalabanCMP116MinimalFixedPointDistanceRound384Exact.agda` projects the fixed-point source theorem to the least-privilege data needed for

```text
d_boundary <= U_par.
```

It deliberately drops R370's historical `boundaryHessianStable` compatibility field, left/right physical Hessian domains and variations. A source-native R371 application can therefore pay fixed-point distance **before** any Hessian theorem.

### R385 — two minimal producers meet only at the selected metric

`BalabanCMP116MinimalDistanceLiteralHessianRound385Exact.agda` composes:

```text
R384 minimal fixed-point distance producer
+
R103 literal CMP116 marked-Hessian Cauchy producer
----------------------------------------------
R379 coefficient comparison.
```

The Hessian Cauchy parameter metric is definitionally the fixed-point output metric. No full R370 record, R380--R383 compatibility chain, historical marked input, or equality of fixed-point and Hessian Lipschitz constants is mandatory.

The surviving local same-object theorem is the scalarization

```text
R373 boundary norm
  = target-space distance between the two literal R103 Hessian values.
```

### R386 — comparison is not absolute localization

`BalabanCMP116ComparisonVsAbsoluteLocalizationRound386Exact.agda` records the terminal firewall. R385 produces a **difference/comparison** estimate. R346/R338/R341 consume an **absolute selected mixed-log / connected-response localization** estimate. A generic exact counterexample shows that endpoint-difference control cannot manufacture endpoint absolute control without another coordinate.

Therefore R385 is an optional subproducer for the literal localization theorem, not the terminal B theorem itself.

The canonical direct source route remains:

```text
published differentiated CMP116 localization
+ selected-J same-object/applicability
+ source-envelope / physical-distance calibration
+ same-family finite->continuum connected-covariance transport
-> quantitative continuum clustering
-> existing clustering->gap compiler.
```

## Current preferred live payments after R386

### Canonical B-facing payments

```text
B1 literal selected differentiated localization:
   published/source CMP116 response on the SAME selected T5 J-pair,
   SAME active density, SAME root and SAME physical support distance;

B2 selected physical distance = Euclidean spectral time;

B3 same-family finite -> continuum connected-covariance transport;

B4 existing clustering -> positive transfer-gap compiler.
```

### Optional coefficient/sensitivity producer payments

If the R385 producer is used to help manufacture B1, its remaining source-facing coordinates are:

```text
P1 selected published fixed-point family/domain attachment;
P2 source parameter-distance calibration;
P3 literal R103 Hessian analyticity/magnitude/radius/common-neighbourhood payment;
P4 literal boundary-norm -> Hessian-target-distance scalarization;
P5 R348 coefficient/mixed-log same-object attachment;
P6 an absolute anchor/reference or an independent absolute source-localization theorem.
```

P6 is mandatory for promoting a comparison into an absolute localization; R385 alone cannot supply it.

For consumers that semantically require the historical marked coordinate, add the optional compatibility payment

```text
U_par <= M_marked^src
```

and use R378/R351/R377/R376.

## What is no longer primitive debt

Do not schedule as independent mathematics:

- full two-fixed-point H_sub after R370/R384;
- R370's compatibility `boundaryHessianStable` merely to obtain fixed-point distance;
- CMP99 marked propagator comparison as direct fixed-point displacement;
- CMP102 C-Lipschitz merely to obtain fixed-parameter contraction;
- affine subtraction algebra after R369;
- equality of two source contraction balls;
- a new D³/Hessian Lipschitz theorem after R372;
- a second Hessian-family identity after R103/R375/R383;
- a separate radius for first- and second-derivative consumers after R374;
- a duplicate R373/R370 selected-distance equality after R381/R384;
- R351 `d_sub <= M_marked` as a primitive theorem after R378;
- historical marked-input calibration as a requirement of R375 after R379;
- equality of fixed-point and Hessian Lipschitz constants;
- promotion of coefficient-difference control to absolute selected localization without an anchor/source theorem.

## Attachment / Aristotle donor interpretation

The supplied `ym-clay-final-output-20260916` bundle is useful as a producer donor, not as Agda theorem authority. In particular its Lean `CMP116ActivityRate`, `MarkedPolymerDecay`, `RowBShellEnergy`, `PolymerActivityDecay`, `WeightedInfluenceRows`, and `RowBToRowCTemporalFusion` files show that, **once** the literal differentiated CMP116 activity majorant is supplied, block-size cancellation, entropy competition, marked-activity polynomial cost, geometric shell summation and several Row-B/Row-C consequences are compiler/theorem output with explicit constants.

The bundle itself remains fail-closed at the same physical point: the literal differentiated CMP116 activity/source majorant (`hact` / same-object source identification) is still an input. This reinforces the present consumer-first cut rather than closing it.

## Broader lane separation

Current BC1 source lane and current mass-gap sensitivity lane remain distinct:

```text
BC1:
  P0 CMP122 witness + P1 D² + P2 CMP109 Eq.(5.1) + P3 normalized CMP116 demands.

mass-gap direct B:
  literal selected differentiated localization
  + D_time
  + same-family covariance limit
  + clustering->gap.

optional coefficient producer:
  R384 minimal fixed-point distance
  + literal Hessian Cauchy sensitivity
  + R385 comparison
  + C_attach / anchor as required.
```

Do not merge these queues merely because all mention CMP116.

### BC1 source lane retained from the #949 form-flow pass

The active raw-to-BC1 route remains a lower-level source/representation lane,
not the present mass-gap terminal consumer.  Its compact preferred path is:

```text
finite-history raw CMP119 objects
  -> concrete Sect.-2 predicate family
       ELocalizedAnalytic := exact same-E localization record
  -> genuine CMP122 Theorem-1 witness on that concrete family
  -> identity E-localization decoder
  -> active raw Sect.-2 witness
  -> active regular-E/localization form
  -> active CMP109/CMP116 continuation
  -> BC1 representation.
```

On that route, decoder/raw-witness assembly, regular-E form projection, active
continuation, common-radius construction, and BC1 same-E identity are compiler
or representation plumbing, not primitive payments.  The theorem-bearing BC1
inputs after representation remain the genuine selected CMP122 witness, physical
SecondVariationLinearity on the exact active `E_k` carrier, literal CMP109
Eq.(5.1) binding on that same continuation, and literal extraction of the
finite normalized CMP116 analytic demands.

## Primary source coordinates retained

- CMP99 — Bałaban, *Propagators for Lattice Gauge Theories in a Background Field*, DOI `10.1007/BF01240355`.
- CMP102 — Bałaban, *The Variational Problem and Background Fields in Renormalization Group Method for Lattice Gauge Theories*, DOI `10.1007/BF01229381`.
- CMP109 — Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories I*, DOI `10.1007/BF01215223`.
- CMP116 — Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories II. Cluster Expansions*, DOI `10.1007/BF01239022`.
- CMP119 — Bałaban, *Convergent Renormalization Expansions for Lattice Gauge Theories*, DOI `10.1007/BF01217741`.
- CMP122 I — DOI `10.1007/BF01257412`.
- CMP122 II — DOI `10.1007/BF01238433`.

Person QID / exact paper-specific Dewey remain unresolved unless an authoritative identity/catalogue source is acquired. Do not guess them.

## Exact-head snapshot

The exact branch head and combined status are queried directly from GitHub; do not infer them from internal round commit labels.

## Validation boundary

This is navigation/status only. R368--R386 are source-written reductions unless an exact-head Agda/kernel receipt says otherwise. Repository `machineChecked` / `standardImported` labels are not fresh kernel receipts. Source text or an external Lean donor does not create selected same-object inhabitants. No continuum YM construction, physical mass-gap theorem, Clay promotion, or external acceptance is claimed here.
