# Yang–Mills CMP Work Status

Status: navigation / archaeology companion to `YMRHPRRoundArchaeologyAudit.md`. **Not theorem authority and not a Clay-completion claim.**

Purpose: stop repeated proof-search from treating `CMP99`, `CMP102`, `CMP109`, `CMP116`, `CMP119`, or `CMP122` as one undifferentiated open task. The paper-level source authority, most carrier dictionaries, and downstream compiler plumbing have already been developed across many PRs. Future Pareto search should reopen a CMP-labelled object only when a current consumer exposes a specific unpaid same-object physical/source instantiation.

## Executive rule

**DO NOT reopen “formalise CMP109/116/119/122” as a generic task.**

Use this classification instead:

| Source family | Repository status for current search | What is already owned | What may still be legitimately open |
|---|---|---|---|
| CMP99 | SOURCE PROPAGATOR AUTHORITY OWNED | regular-background Green/gradient bounds, analytic background dependence, marked domain-sequence propagator comparison / discrepancy-decay source boundary | exact attachment of the published marked propagator-difference theorem to a selected later `H(s(Y0))` carrier; not a direct fixed-point displacement theorem |
| CMP102 | SOURCE VARIATIONAL/BACKGROUND AUTHORITY OWNED | background criticality/minimization/uniqueness modulo gauge, analyticity/locality/derivative locality, common source radius; source contraction/locality proof behind the nonlinear background map | exact same-object identification of the literal nonlinear critical-map `C` and a proof-bearing quantitative contraction/Lipschitz receipt on the selected CMP116 carrier |
| CMP109 | SOURCE/COMPILER LARGELY OWNED | regular small-field effective-action lane, differentiated coordinate machinery, Eq.(5.1)-facing continuation interfaces, downstream BC/response compilers | a *specific literal physical differential/source identification* required by a live consumer; not CMP109 as a whole |
| CMP116 | SOURCE/COMPILER LARGELY OWNED | localization/cluster-expansion continuation, marked-source/localization machinery, literal substituted-background fixed-point equation, common small-ball contraction construction, common continuation interfaces, Row-C donor machinery | a *specific carrier realization, same-object propagator/map/operation attachment, marked-row or quantitative physical estimate* demanded by the current consumer |
| CMP119 | SOURCE OBJECT/DICTIONARY LARGELY OWNED | complete-density dictionary, raw source state, finite-beta construction, `rho_k/U_k/E_k/R_k/B_k/A_k/vacuum` vocabulary, Eq.(2.23), function-valued regular `E_k`, selected regular-E projection, source-localization interface | exact same-object realization of a selected physical carrier if not already attached; do not reconstruct the complete-density theory merely because a later wrapper is conditional |
| CMP122 | PUBLISHED THEOREM BOUNDARY OWNED | Theorem-1/UV-stability authority, finite-history coupling hypothesis, active-scale source theorem carrier, raw-CMP119 active specialization | theorem-bearing exact instantiation on a selected source family if a current consumer lacks it; continuum/OS/mass-gap consequences remain separate and are **not** supplied by CMP122 |

## Current live sensitivity recut: R365--R368

This is the present high-alpha CMP99/CMP102/CMP116 application seam on specialist PR #944.

CMP116 Part II, Sect. 1 uses the source equation

```text
D(A') = C(A' - H D(A')).
```

and explicitly places the transformation on one common small ball, shows it maps that ball into itself, and states that it is contractive there. This changes the preferred `H_sub` search substantially.

### R365 — no primitive two-fixed-point displacement

`BalabanCMP116SubstitutionContractionRound365Exact.agda` proves the generic fixed-point perturbation compiler:

```text
d(x_L,x_R) <= q d(x_L,x_R) + delta
```

from one map's contraction plus one cross-parameter map defect evaluated at a common candidate. Scalar absorption turns that into a bound by an amplified `delta`.

Therefore:

```text
full H_subScale theorem as a primitive = dominated.
```

### R366 — source parameter defect factors before fixed-point absorption

`BalabanCMP116OneStepMapDefectRound366Exact.agda` factors the literal source-shaped map defect as

```text
||F_L(X)-F_R(X)||
<= L_C ||(A'-H_L X)-(A'-H_R X)||
<= L_C ||(H_L-H_R)X||
<= L_C M_H ||X||
<= L_C M_H R.
```

This rehabilitates CMP99 only at the correct layer:

```text
CMP99 marked propagator difference
-> possible producer for M_H
-> one-step map defect
-> R365 fixed-point perturbation
-> H_subScale.
```

It is a WrongType to use CMP99 directly as the complete substituted-background displacement theorem.

### R367 — source `C` contraction becomes proof-bearing

`BalabanCMP102CriticalMapLipschitzRound367Exact.agda` replaces a free scalar `L_C` inequality with a proof-bearing source theorem surface on the exact nonlinear map:

```text
d(C x,C y) <= L_C d(x,y)
```

for arguments inside the declared source ball.

Important distinction:

```text
PublishedVariationalBackgroundAuthority.backgroundAnalytic
!=
a quantitative C-Lipschitz proof.
```

Source analyticity/locality metadata may motivate the attachment, but only the actual contraction theorem on the same `C` carrier can inhabit the R367 payment.

### R368 — affine argument difference is generic algebra

`BalabanCMP116AffineArgumentDifferenceRound368Exact.agda` removes another false physical primitive.

On an ordinary abelian difference carrier, with operator subtraction acting pointwise, it proves

```text
(A' - H_L X) - (A' - H_R X)
  = (H_R - H_L) X.
```

The common-base cancellation is derived from addition/negation/subtraction laws; the operator step is derived from the generic operator-difference action law. The resulting scalar argument-defect inequality is then reflexive after equality transport.

Therefore:

```text
argumentDefectBelowPropagatorAction
```

is no longer a primitive analytic/source estimate on the preferred route.

What remains source-facing is only the **same-object operation attachment**: the actual CMP116 background subtraction and `H_R-H_L` action must instantiate the generic R368 carrier. R368 does not manufacture that identity from shared notation, and it does not pay the CMP99 quantitative propagator bound or the common source ball.

### Current same-object payments after R368

The local `H_sub` route is now concentrated in:

```text
C_attach^102/116:
  literal CMP102 C == nonlinear C used by selected CMP116/R367 map;

H_attach^99/116:
  published CMP99 marked H_L-H_R theorem == selected CMP116 H(s(Y0)) difference;

operation attachment:
  literal CMP116 background subtraction and operator-difference action
  instantiate the ordinary R368 affine carrier;

radius/common-ball attachment:
  source CMP102/CMP116 invariant ball == selected R365/R367 carrier.
```

The affine identity itself is compiler algebra once the operation semantics are attached. It is no longer a separate physical theorem coordinate.

Once those attachments are paid:

```text
R368 -> R367 -> R366 -> R365 -> R364
```

constructs the selected substitution displacement path.

The likely next genuinely local analytic leaf is then `H_local`:

```text
||D^2 E(H_Omega) - D^2 E(H_Omega')||
  <= L_source d_sub,
```

unless a source-native derivative theorem reduces that too.

## PR chronology that established the broader CMP discipline

### #543 — source-faithful complete-density reuse

`YM Gate I + source-faithful complete-density RG reuse`

This is the major route correction from “rebuild RG1a/RG1b” to “reuse Bałaban's published complete-density theorem”. It introduced/used the CMP119/CMP122 -> existing `CombinedRGAdmissibility` path and explicitly stated that the frontier is literal source-carrier identification rather than another generic cluster/RG theorem.

### #568 — published four-dimensional UV boundary

`YM Round58: canonical G2, compact-group one-loop, and published 4D UV boundary`

This tranche separated raw CMP119 scale-indexed objects/Eq.(2.23), finite-beta-history construction, CMP122 Theorem-1 active-scale specialization, published four-dimensional finite-cutoff UV stability, and later continuum/OS/nontriviality/clustering obligations.

Important conclusion: **published CMP122 UV stability is not a missing DASHI theorem and is not the Clay mass-gap theorem.**

### #821 — broad raw-source wall (historical, later superseded)

This correctly enforced same-object source discipline and separated complete action `A_k` from regular small-field `E_k`, but its broad raw-objects-first route was later made unnecessarily strong for the BC1 consumer.

### #846 onward — consumer-indexed regular-E recut

The preferred BC1 source direction became:

```text
broad CMP reconstruction
-> source-native complete density
-> selected regular E
-> function-valued regular E
-> active-scale regular-E/localization form
-> compiler-owned CMP109/116 -> BC1.
```

Later R248--R250 work strengthens this again: on the preferred concrete Sect.-2 predicate representation, identity decoding, active raw witness assembly, regular-E projection and R247 continuation are compiler-owned. The live BC1 source coordinates are P0 CMP122 theorem witness, P1 physical second variation, P2 literal CMP109 Eq.(5.1) binding and P3 finite normalized CMP116 demand extraction.

Do not conflate that BC1 finite-source-realization lane with the current R365--R368 mass-gap sensitivity lane merely because both mention CMP116.

## What “conditional” means here

A `ProofLevel = conditional` on a late CMP wrapper does **not** imply “CMP theorem missing”. First classify the condition:

1. published source theorem authority missing? usually no for the core imported boundaries;
2. generic compiler missing? frequently already closed;
3. same-object carrier realization missing? potentially yes;
4. literal physical/analytic estimate missing? potentially yes;
5. continuum/OS/mass-gap consequence missing? separate programme.

Only (3) or (4), when demanded by the literal current consumer, should normally survive the Pareto filter.

## Current do-not-reopen list

Unless a current exact consumer demonstrates otherwise, do not spend proof-search budget on:

- re-proving CMP99/CMP102 propagator/variational theory generically;
- re-proving CMP109/CMP116 localization/continuation theory generically;
- re-proving CMP119 complete-density RG theory generically;
- re-proving CMP122 four-dimensional UV stability generically;
- rebuilding generic fixed-point perturbation after R365;
- treating CMP99 marked comparison as direct `H_subScale` payment;
- treating source analyticity as a numerical C-Lipschitz proof;
- proving the R366 affine argument inequality as a new physical theorem after R368;
- confusing the remaining same-object operation attachment with new analysis;
- rebuilding an abstract `RegularTerm` instead of function-valued `E_k`;
- treating complete action `A_k` as the object differentiated by CMP109 Eq.(5.1);
- treating CMP122 UV stability as continuum Schwinger construction, OS reconstruction, nontriviality, clustering, or physical mass gap.

## Live-search rule

When YM Pareto search lands on a CMP-labelled conditional, ask:

```text
Which exact current consumer?
Which exact selected source object?
Which same-object equality/physical estimate is absent?
Was that equality already paid under an earlier/later round alias?
Is the apparent theorem actually compiler algebra after same-object attachment?
```

Only search the wider PR history if the current board/status files do not answer those questions.

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

This file is navigation/status only. R365--R368 are source-written reductions; repository `machineChecked`/`standardImported` labels are not fresh exact-head kernel receipts. Source text and citation authority do not create same-object Agda inhabitants. No continuum Yang--Mills construction, physical mass-gap theorem, Clay promotion, or RH proof is claimed here.
