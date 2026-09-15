# Yang–Mills CMP Work Status

Status: navigation / archaeology companion to `YMRHPRRoundArchaeologyAudit.md`. **Not theorem authority and not a Clay-completion claim.**

Purpose: stop repeated proof-search from treating `CMP99`, `CMP102`, `CMP109`, `CMP116`, `CMP119`, or `CMP122` as one undifferentiated open task. The paper-level source authority, most carrier dictionaries, and downstream compiler plumbing have already been developed across many PRs. Future Pareto search should reopen a CMP-labelled object only when a current consumer exposes a specific unpaid same-object physical/source instantiation.

## Executive rule

**DO NOT reopen “formalise CMP109/116/119/122” as a generic task.**

| Source family | Repository status for current search | What is already owned | What may still be legitimately open |
|---|---|---|---|
| CMP99 | SOURCE PROPAGATOR AUTHORITY OWNED | regular-background Green/gradient bounds, analytic background dependence, marked domain-sequence propagator comparison / discrepancy-decay source boundary | exact attachment of the published marked propagator-difference theorem to the selected `H(s(Y0))` carrier |
| CMP102 | SOURCE VARIATIONAL/BACKGROUND AUTHORITY OWNED | background criticality/minimization/uniqueness modulo gauge, analyticity/locality/derivative locality, common source radius; source contraction/locality proof shape | exact `C` identification only if R367 is used as the cross-parameter sensitivity producer |
| CMP109 | SOURCE/COMPILER LARGELY OWNED | regular small-field effective-action lane, differentiated coordinate machinery, Eq.(5.1)-facing continuation interfaces, downstream BC/response compilers | a specific literal physical differential/source identification demanded by a live consumer |
| CMP116 | SOURCE/COMPILER LARGELY OWNED | localization/cluster-expansion continuation, marked-source/localization machinery, literal substituted-background equation, fixed-parameter contraction-ball construction, common continuation interfaces | selected same-object propagator/operation attachment, one-sided cross-membership, cross-parameter defect, or other literal quantitative estimate demanded by the current consumer |
| CMP119 | SOURCE OBJECT/DICTIONARY LARGELY OWNED | complete-density dictionary, finite-beta construction, raw source state, function-valued regular `E_k`, selected regular-E projection, source-localization interface | exact selected physical realization only when still demanded downstream |
| CMP122 | PUBLISHED THEOREM BOUNDARY OWNED | Theorem-1/UV-stability authority, finite-history coupling hypothesis, active-scale source theorem carrier | theorem-bearing exact instantiation on selected source family; continuum/OS/mass-gap consequences remain separate |

## Current live sensitivity recut: R365--R370

CMP116 Part II, Sect. 1 uses

```text
D(A') = C(A' - H D(A')).
```

The current direct sensitivity route separates four logically different layers: fixed-parameter contraction, cross-parameter map defect, affine/operator algebra, and source-domain overlap.

### R365 — fixed-point displacement is compiler-owned

`BalabanCMP116SubstitutionContractionRound365Exact.agda` proves

```text
d(x_L,x_R) <= q d(x_L,x_R) + delta
```

from contraction of the left map and one cross-parameter defect at the common candidate. Scalar absorption then bounds the displacement by an amplified `delta`.

### R366 — factor the cross-parameter defect

`BalabanCMP116OneStepMapDefectRound366Exact.agda` factors

```text
||F_L(X)-F_R(X)||
<= L_C ||(A'-H_L X)-(A'-H_R X)||
<= L_C ||(H_L-H_R)X||
<= L_C M_H ||X||
<= L_C M_H R.
```

CMP99 belongs at the `M_H` propagator-difference layer, not as the complete fixed-point displacement theorem.

### R367 — optional proof-bearing cross-parameter C producer

`BalabanCMP102CriticalMapLipschitzRound367Exact.agda` turns the C stage into a proof-bearing source theorem

```text
d(C x,C y) <= L_C d(x,y).
```

It is a valid producer if the exact C attachment is supplied. Analyticity/locality metadata alone do not pay it.

### R368 — direct fixed-parameter CMP116 composite contraction

`BalabanCMP116DirectDecoupledContractionRound368Exact.agda` imports the source theorem directly on

```text
F_s(X) = C(A' - H(s)X).
```

Each parameter has a source ball on which the literal composite map preserves the ball and contracts with factor `<1`. Therefore a CMP102→CMP116 C identity is **not mandatory merely to obtain the same-parameter contraction factor**.

R368 does not pay cross-parameter sensitivity.

### R369 — affine cross-parameter argument difference is generic algebra

`BalabanCMP116AffineArgumentDifferenceRound369Exact.agda` derives

```text
(A' - H_L X) - (A' - H_R X)
  = (H_R - H_L) X
```

from abelian difference laws plus pointwise operator subtraction. The scalar argument-defect inequality follows by equality transport/reflexivity.

Thus only the actual CMP116 operation same-object attachment remains; no new analytic affine inequality is scheduled.

### R370 — common-ball equality is stronger than the perturbation proof needs

`BalabanCMP116OneSidedBallPerturbationRound370Exact.agda` compares R365 with the direct R368 source balls.

R365 contracts only the left map between the two fixed points. Hence it needs

```text
leftPoint  ∈ sourceBall(leftParameter)
rightPoint ∈ sourceBall(leftParameter)
```

plus each point's own fixed-point equation and the cross-parameter map defect. It does **not** require

```text
sourceBall(leftParameter) = sourceBall(rightParameter).
```

R370 compiles the direct R368 source maps/balls into R365 using exactly this one-sided cross-membership interface.

Therefore the old “common ball equality” scheduling item is Pareto-dominated. The remaining source/domain payment is the concrete right-fixed-point-in-left-source-ball statement (or any stronger source theorem that implies it).

### Current live payments after R370

```text
H_attach^99/116:
  CMP99 marked H_L-H_R authority == selected CMP116 H(s(Y0)) difference;

cross-parameter C sensitivity:
  R367 + exact C attachment is the current proof-bearing producer,
  unless a more direct CMP116 composite-map parameter theorem is recovered;

operation attachment:
  actual CMP116 subtraction/operator difference == R369 affine carrier;

one-sided source-ball cross-membership:
  right fixed point lies in the left source contraction ball.
```

Fixed-parameter contraction, affine cancellation, and equality of the two balls are no longer primitive debts.

The next genuinely local analytic branch remains `H_local`:

```text
||D^2 E(H_Omega) - D^2 E(H_Omega')|| <= L_source d_sub,
```

unless source-native derivative archaeology reduces it too.

## Broader CMP chronology / lane separation

- **#543**: source-faithful complete-density reuse; stop rebuilding generic RG.
- **#568 / Round58**: raw CMP119 state + finite-beta source history + CMP122 active Theorem-1 / published UV boundary.
- **#821**: broad raw-source wall; historically important but later too strong for BC1.
- **#846 onward / R215→R250**: consumer-indexed regular-E route; function-valued `E_k`, localization, active source form, R248 identity decoder and R250 preferred concrete continuation.

Current BC1 source lane and current mass-gap sensitivity lane remain distinct:

```text
BC1: P0 CMP122 witness + P1 D² + P2 CMP109 Eq.(5.1) + P3 normalized CMP116 demands.

mass-gap H_sub: R368 fixed contraction + R369 affine algebra + R370 one-sided ball
                + true cross-parameter/H attachments.
```

Do not merge these queues merely because both mention CMP116.

## Current do-not-reopen list

Do not spend proof-search budget on:

- generic re-proofs of CMP99/CMP102/CMP109/CMP116/CMP119/CMP122;
- full two-fixed-point `H_subScale` after R365;
- CMP99 marked comparison as direct fixed-point displacement;
- source analyticity as a numerical C-Lipschitz proof;
- a cross-paper C identity merely to recover fixed-parameter contraction after R368;
- the affine R366 inequality as new physics after R369;
- equality of the two source contraction balls after R370;
- generic operator algebra detached from the actual same-object operation attachment;
- abstract `RegularTerm` reconstruction instead of function-valued `E_k`;
- complete `A_k` as the object differentiated by CMP109 Eq.(5.1);
- CMP122 UV stability as continuum Schwinger construction, OS reconstruction, clustering or physical mass gap.

## Live-search rule

When a CMP-labelled conditional appears, ask:

```text
Which exact consumer?
Which selected source object?
Which same-object equality or physical estimate is absent?
Is a stronger condition being requested than the compiler actually consumes?
Was the apparent theorem already reduced under another round alias?
```

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

This is navigation/status only. R365--R370 are source-written reductions; repository `machineChecked` / `standardImported` labels are not fresh exact-head kernel receipts. Source text does not create same-object Agda inhabitants. No continuum YM construction, physical mass-gap theorem, Clay promotion, or RH proof is claimed here.
