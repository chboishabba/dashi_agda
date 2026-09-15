# Yang–Mills CMP Work Status

Status: navigation / archaeology companion to `YMRHPRRoundArchaeologyAudit.md`. **Not theorem authority and not a Clay-completion claim.**

Purpose: stop repeated proof-search from treating `CMP99`, `CMP102`, `CMP109`, `CMP116`, `CMP119`, or `CMP122` as one undifferentiated open task. The paper-level source authority, most carrier dictionaries, and downstream compiler plumbing have already been developed across many PRs. Future Pareto search should reopen a CMP-labelled object only when a current consumer exposes a specific unpaid same-object physical/source instantiation.

## Executive rule

**DO NOT reopen “formalise CMP109/116/119/122” as a generic task.**

Use this classification instead:

| Source family | Repository status for current search | What is already owned | What may still be legitimately open |
|---|---|---|---|
| CMP99 | SOURCE PROPAGATOR AUTHORITY OWNED | regular-background Green/gradient bounds, analytic background dependence, marked domain-sequence propagator comparison / discrepancy-decay source boundary | exact attachment of the published marked propagator-difference theorem to a selected later `H(s(Y0))` carrier; not a direct fixed-point displacement theorem |
| CMP102 | SOURCE VARIATIONAL/BACKGROUND AUTHORITY OWNED | background criticality/minimization/uniqueness modulo gauge, analyticity/locality/derivative locality, common source radius; source contraction/locality proof behind the nonlinear background map | exact same-object identification of the literal nonlinear critical-map `C` only where a cross-parameter `C`-Lipschitz producer is actually used |
| CMP109 | SOURCE/COMPILER LARGELY OWNED | regular small-field effective-action lane, differentiated coordinate machinery, Eq.(5.1)-facing continuation interfaces, downstream BC/response compilers | a *specific literal physical differential/source identification* required by a live consumer; not CMP109 as a whole |
| CMP116 | SOURCE/COMPILER LARGELY OWNED | localization/cluster-expansion continuation, marked-source/localization machinery, literal substituted-background fixed-point equation, fixed-parameter small-ball contraction construction, common continuation interfaces, Row-C donor machinery | specific same-object decoupled-map, propagator, operation, cross-parameter or common-ball attachments demanded by the current consumer |
| CMP119 | SOURCE OBJECT/DICTIONARY LARGELY OWNED | complete-density dictionary, raw source state, finite-beta construction, `rho_k/U_k/E_k/R_k/B_k/A_k/vacuum` vocabulary, Eq.(2.23), function-valued regular `E_k`, selected regular-E projection, source-localization interface | exact same-object realization of a selected physical carrier if not already attached; do not reconstruct the complete-density theory merely because a later wrapper is conditional |
| CMP122 | PUBLISHED THEOREM BOUNDARY OWNED | Theorem-1/UV-stability authority, finite-history coupling hypothesis, active-scale source theorem carrier, raw-CMP119 active specialization | theorem-bearing exact instantiation on a selected source family if a current consumer lacks it; continuum/OS/mass-gap consequences remain separate and are **not** supplied by CMP122 |

## Current live sensitivity recut: R365--R369

This is the present high-alpha CMP99/CMP102/CMP116 application seam on specialist PR #944.

CMP116 Part II, Sect. 1 uses

```text
D(A') = C(A' - H D(A')).
```

The source distinguishes two different facts that must stay typed separately:

1. for each fixed decoupling parameter, the composite map `F_s(X)=C(A'-H(s)X)` preserves its source ball and contracts there;
2. comparing two different parameters requires a cross-parameter defect estimate.

### R365 — no primitive two-fixed-point displacement

`BalabanCMP116SubstitutionContractionRound365Exact.agda` proves the generic fixed-point perturbation compiler

```text
d(x_L,x_R) <= q d(x_L,x_R) + delta
```

from same-parameter contraction plus one cross-parameter map defect at a common candidate. Scalar absorption turns this into a bound by an amplified `delta`.

### R366 — cross-parameter map defect factors

`BalabanCMP116OneStepMapDefectRound366Exact.agda` factors

```text
||F_L(X)-F_R(X)||
<= L_C ||(A'-H_L X)-(A'-H_R X)||
<= L_C ||(H_L-H_R)X||
<= L_C M_H ||X||
<= L_C M_H R.
```

CMP99 is a legitimate upstream producer for `M_H`, not the full fixed-point displacement theorem.

### R367 — optional proof-bearing cross-parameter `C` producer

`BalabanCMP102CriticalMapLipschitzRound367Exact.agda` makes the `C` stage proof-bearing:

```text
d(C x,C y) <= L_C d(x,y)
```

inside a declared source ball.

Firewall:

```text
background analyticity/locality status != quantitative C-Lipschitz proof.
```

R367 is a valid producer for the cross-parameter defect if the exact CMP102/CMP116 `C` same-object attachment is supplied. It is **not** required merely to recover the same-parameter source contraction, because R368 below imports that directly from CMP116.

### R368 — direct fixed-parameter CMP116 composite contraction

`BalabanCMP116DirectDecoupledContractionRound368Exact.agda` records the source-shaped fixed-parameter theorem directly on

```text
F_s(X) = C(A' - H(s)X).
```

For each parameter it exposes the literal source map, its invariant contraction ball, map preservation, contraction and factor `< 1`. This pays the R365 same-parameter contraction side without first identifying a separate CMP102 `C` carrier.

It deliberately does **not** pay the cross-parameter defect `F_L(X)-F_R(X)`. A common ball across two parameters and the actual cross-parameter sensitivity remain separate.

Thus:

```text
CMP102->CMP116 C identity is not mandatory for fixed-parameter contraction;
R367 remains an optional cross-parameter producer.
```

### R369 — affine cross-parameter argument difference is generic algebra

`BalabanCMP116AffineArgumentDifferenceRound369Exact.agda` removes another false physical primitive.

From ordinary abelian addition/negation/subtraction laws plus pointwise operator subtraction it proves

```text
(A' - H_L X) - (A' - H_R X)
  = (H_R - H_L) X.
```

The scalar `argumentDefectBelowPropagatorAction` inequality then follows by equality transport and reflexivity.

The source-facing coordinate is only the same-object operation attachment: the actual CMP116 background subtraction and `H_R-H_L` action must instantiate this generic carrier. R369 does not pay the CMP99 quantitative propagator comparison or the common-ball requirement.

### Current same-object payments after R369

The local `H_sub` route is now concentrated in:

```text
H_attach^99/116:
  published CMP99 marked H_L-H_R theorem == selected CMP116 H(s(Y0)) difference;

operation attachment:
  literal CMP116 background subtraction and operator-difference action
  instantiate the ordinary R369 affine carrier;

common-ball attachment:
  the two selected source parameters are admissible in the common comparison
  context required by R365/cross-parameter sensitivity;

cross-parameter C sensitivity producer:
  either use R367 with exact C attachment, or find a still more direct CMP116
  source theorem on the composite parameter defect.
```

The same-parameter contraction itself is no longer waiting on `C_attach^102/116`; R368 handles that source fact directly.

The likely next genuinely local analytic leaf after `H_sub` is `H_local`:

```text
||D^2 E(H_Omega) - D^2 E(H_Omega')||
  <= L_source d_sub,
```

unless a source-native derivative theorem reduces it further.

## PR chronology that established the broader CMP discipline

### #543 — source-faithful complete-density reuse

`YM Gate I + source-faithful complete-density RG reuse`

Major correction from rebuilding generic RG machinery to reusing Bałaban's complete-density theorem and isolating literal source-carrier identification.

### #568 — published four-dimensional UV boundary

`YM Round58: canonical G2, compact-group one-loop, and published 4D UV boundary`

Separated raw CMP119 objects, finite-beta history, CMP122 active-scale specialization, published finite-cutoff UV stability, and the genuinely later continuum/OS/nontriviality/clustering obligations.

### #821 — broad raw-source wall (historical, later superseded)

Correctly enforced same-object discipline and separated complete `A_k` from regular `E_k`, but its raw-objects-first route became too strong for BC1.

### #846 onward — consumer-indexed regular-E recut

The preferred BC1 direction became

```text
source-native complete density
-> selected/function-valued regular E
-> active regular-E/localization form
-> compiler-owned CMP109/116 -> BC1.
```

R248--R250 strengthen this again: identity decoding, active raw witness assembly, regular-E projection and R247 continuation are compiler-owned on the preferred concrete predicate representation. The live BC1 coordinates are P0 CMP122 theorem witness, P1 physical second variation, P2 literal CMP109 Eq.(5.1) binding and P3 finite normalized CMP116 demand extraction.

Do not conflate that BC1 source-realization lane with the R365--R369 mass-gap sensitivity lane merely because both mention CMP116.

## What “conditional” means here

A late `conditional` CMP wrapper does not mean “the CMP theorem is missing”. Classify it as source authority, generic compiler, same-object carrier realization, literal physical estimate, or later continuum/OS/mass-gap consequence. Only current-consumer instances of the latter two should normally survive Pareto pruning.

## Current do-not-reopen list

Do not spend proof-search budget on:

- re-proving CMP99/CMP102 propagator/variational theory generically;
- re-proving CMP109/CMP116 localization/continuation theory generically;
- re-proving CMP119 complete-density RG theory generically;
- re-proving CMP122 four-dimensional UV stability generically;
- rebuilding generic fixed-point perturbation after R365;
- treating CMP99 marked comparison as direct `H_subScale` payment;
- treating source analyticity as a numerical C-Lipschitz proof;
- requiring a cross-paper `C` identity merely to get fixed-parameter contraction after R368;
- proving the R366 affine argument inequality as new physics after R369;
- confusing R369's generic algebra with the still-required same-object operation attachment;
- rebuilding abstract `RegularTerm` instead of function-valued `E_k`;
- treating complete `A_k` as the object differentiated by CMP109 Eq.(5.1);
- treating CMP122 UV stability as continuum Schwinger construction, OS reconstruction, nontriviality, clustering, or physical mass gap.

## Live-search rule

When Pareto search lands on a CMP-labelled conditional, ask:

```text
Which exact current consumer?
Which exact selected source object?
Which same-object equality/physical estimate is absent?
Was it already paid under an earlier/later round alias?
Is the apparent theorem generic compiler algebra after same-object attachment?
```

## Primary source coordinates retained

- CMP99 — Bałaban, *Propagators for Lattice Gauge Theories in a Background Field*, DOI `10.1007/BF01240355`.
- CMP102 — Bałaban, *The Variational Problem and Background Fields in Renormalization Group Method for Lattice Gauge Theories*, DOI `10.1007/BF01229381`.
- CMP109 — Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories I*, DOI `10.1007/BF01215223`.
- CMP116 — Bałaban, *Renormalization Group Approach to Lattice Gauge Field Theories II. Cluster Expansions*, DOI `10.1007/BF01239022`.
- CMP119 — Bałaban, *Convergent Renormalization Expansions for Lattice Gauge Theories*, DOI `10.1007/BF01217741`.
- CMP122 I — Bałaban, *Large Field Renormalization I: The Basic Step of the R-Operation*, DOI `10.1007/BF01257412`.
- CMP122 II — Bałaban, *Large Field Renormalization II: Localization, Exponentiation, and Bounds for the R Operation*, DOI `10.1007/BF01238433`.

Person QID / exact paper-specific Dewey remain unresolved unless an authoritative identity/catalogue source is acquired. Do not guess them.

## Validation boundary

This file is navigation/status only. R365--R369 are source-written reductions; repository `machineChecked`/`standardImported` labels are not fresh exact-head kernel receipts. Source text and citation authority do not create same-object Agda inhabitants. No continuum Yang--Mills construction, physical mass-gap theorem, Clay promotion, or RH proof is claimed here.
