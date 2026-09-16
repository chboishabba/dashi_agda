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

## Current live sensitivity recut: R368--R380

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

Result:

```text
||Delta H_coeff|| <= L_Hessian * U.
```

The historical mark is not identified or manufactured.

### R380 — R370 upper feeds R379 directly

`BalabanCMP116ParametricDistanceUpperHessianRound380Exact.agda` instantiates

```text
U := U_par = L_par * d_parameter.
```

The only new preferred-route same-object coordinate is

```text
d_selected^R373(s)
  = d_boundary^R370(iota s).
```

After that equality, R370's existing upper gives the R379 premise, and R375 gives the coefficient bound.

So the preferred local route is now

```text
CMP116 published parametric family
-> R371
-> R370
-> [R373 <-> R370 selected-boundary same-object map]
-> R380
-> R379
-> R375 coefficient/Hessian payment.
```

The R351--R378 historical-mark route remains available but is **not mandatory for this coefficient consumer**.

## Current preferred live payments after R380

```text
P1 selected fixed-point family attachment:
   published CMP116 D(H(s(Y0)),A') / H_k(s(Y0),B')
   == selected R370 family;

P2 selected local-Hessian family attachment:
   published differentiated CMP109/CMP116 activity
   == selected R372/R373 family;

P3 common source-domain/radius/magnitude application:
   selected points lie in the source complex neighbourhood and use the
   source quantitative radius/magnitude data;

P4 selected parameter-distance calibration:
   parameterDistance(left,right) <= sourceParameterDistance;

P5 selected boundary-distance same-object map:
   d_selected^R373(s) = d_boundary^R370(iota s).
```

For consumers that semantically require the historical marked coordinate, add the optional compatibility payment

```text
U_par <= M_marked^src
```

and use R378/R351/R377/R376.

## What is no longer primitive debt

Do not schedule as independent mathematics:

- full two-fixed-point H_sub after R370;
- CMP99 marked propagator comparison as direct fixed-point displacement;
- CMP102 C-Lipschitz merely to obtain fixed-parameter contraction;
- affine subtraction algebra after R369;
- equality of two source contraction balls;
- a new D³/Hessian Lipschitz theorem after R372;
- a second Hessian-family identity after R103/R375;
- a separate radius for first- and second-derivative consumers after R374;
- a duplicate selected R351/R373 distance equality after R377;
- R351 `d_sub <= M_marked` as a primitive theorem after R378;
- **historical marked-input calibration as a requirement of R375 after R379/R380**.

## Broader lane separation

Current BC1 source lane and current mass-gap sensitivity lane remain distinct:

```text
BC1:
  P0 CMP122 witness + P1 D² + P2 CMP109 Eq.(5.1) + P3 normalized CMP116 demands.

mass-gap direct sensitivity:
  R371/R370 parametric fixed-point sensitivity
  + R372/R373 local-Hessian sensitivity
  + R374 common radius
  + R380/R379/R375 direct coefficient payment.
```

Do not merge these queues merely because both mention CMP116.

## Primary source coordinates retained

- CMP99 — Bałaban, *Propagators for Lattice Gauge Theories in a Background Field*, DOI `10.1007/BF01240355`.
- CMP102 — Bałaban, *The Variational Problem and Background Fields in Renormalization Group Method for Lattice Gauge Theories*, DOI `10.1007/BF01229381`.
- CMP109 — Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories I*, DOI `10.1007/BF01215223`.
- CMP116 — Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories II. Cluster Expansions*, DOI `10.1007/BF01239022`.
- CMP119 — Bałaban, *Convergent Renormalization Expansions for Lattice Gauge Theories*, DOI `10.1007/BF01217741`.
- CMP122 I — DOI `10.1007/BF01257412`.
- CMP122 II — DOI `10.1007/BF01238433`.

Person QID / exact paper-specific Dewey remain unresolved unless an authoritative identity/catalogue source is acquired. Do not guess them.

## Validation boundary

This is navigation/status only. R368--R380 are source-written reductions unless an exact-head Agda/kernel receipt says otherwise. Repository `machineChecked` / `standardImported` labels are not fresh kernel receipts. Source text does not create same-object inhabitants. No continuum YM construction, physical mass-gap theorem, Clay promotion, or RH proof is claimed here.
