# Paper 0 Submission Draft: Shared Margin Grammar

## Working Title

Fail-Closed Margin Grammar for Scale-Resolved Physical Closure

## Abstract

We present a small typed grammar for conditional absorption arguments across
scale-resolved physical systems.  The grammar separates residual, production,
absorption, ratio, and signed margin data, and proves the domain-independent
rule:

```text
R'(t) <= P(t) - A(t)
P(t) <= theta A(t)
theta < 1
A(t) > 0
--------------------------------
R'(t) <= -(1-theta) A(t) < 0
```

The proof is intentionally domain-free.  Navier-Stokes, Yang-Mills, and Gate 3
carrier-to-continuum transfer are treated only as non-promoting instantiations:
each lane must separately prove that its ratio is actual, its absorber is
positive, its dynamics bound is discharged, and its strict margin is a theorem
rather than a diagnostic.  The Agda receipts enforce the promotion boundary:
finite diagnostics, toy ratios, finite frame bounds, and carrier gaps are not
promoted to continuum theorems.

## Checked Agda Spine

The Paper 0 spine is:

| Role | Agda receipt | Canonical witness / guard |
|---|---|---|
| L0 grammar | `DASHI.Physics.Closure.StrictMarginImpliesAbsorptionReceipt` | `canonicalStrictMarginImpliesAbsorptionReceipt`; `clayPromotion = false` |
| Terminology and forbidden uses | `DASHI.Physics.Closure.KeyTermCorrespondenceIndexReceipt` | `canonicalKeyTermCorrespondenceIndexReceipt`; `canonicalIndexNoClayPromotion` |
| CM/Hecke partition fence | `DASHI.Physics.Closure.HeckeCarrierVsCMSplittingReceipt` | `canonicalHeckeCarrierVsCMSplittingReceipt`; `canonicalHeckeCMNotSamePartition`; `canonicalHeckeCMNoClayPromotion` |
| `p71` sign-lane boundary | `DASHI.Physics.Closure.P71HeckeMirrorSignLaneReceipt` | `canonicalP71HeckeMirrorSignLaneReceipt`; `canonicalP71IsSplitNotInert`; `canonicalP71NoTimeTheorem`; `canonicalP71NoClayPromotion` |
| Paper 0 consolidation | `DASHI.Physics.Closure.Paper0SharedMarginGrammarConsolidationReceipt` | `canonicalPaper0SharedMarginGrammarConsolidationReceipt`; `canonicalPaper0NoClayPromotion` |
| Edge-accounting target | `DASHI.Physics.Closure.DangerScaleEdgeConservationReceipt` | `canonicalDangerScaleEdgeConservationReceipt`; `canonicalDangerScaleEdgeConservationNoProof` |
| Barrier target | `DASHI.Physics.Closure.ScaleGraphBarrierTargetReceipt` | `canonicalScaleGraphBarrierTargetReceipt`; `canonicalScaleGraphBarrierNotProved` |
| Universal finish shape | `DASHI.Physics.Closure.UniversalScaleGraphBarrierTargetReceipt` | `canonicalUniversalScaleGraphBarrierTargetReceipt`; `canonicalBarrierTargetNotProved` |

## Core Theorem

Paper 0 proves only the shared grammar theorem.  In the Agda surface this is
the content of `StrictMarginImpliesAbsorptionReceipt` and is consolidated by
`Paper0SharedMarginGrammarConsolidationReceipt`.

The theorem has four load-bearing premises:

- `R'(t) <= P(t) - A(t)`: residual dynamics are bounded by production minus
  absorption.
- `P(t) <= theta A(t)`: production is bounded by a ratio times actual
  absorption.
- `theta < 1`: the ratio is strictly subcritical.
- `A(t) > 0`: the absorber is nondegenerate.

Only then may the lane consume absorption:

```text
R'(t) <= -(1 - theta) A(t) < 0
```

The grammar explicitly rejects the following promotion errors:

- diagnostic margin as theorem;
- toy ratio as analytic margin;
- finite frame bound as continuum density;
- observed margin as proved margin;
- carrier gap as continuum gap.

Paper 0 also fixes the partition vocabulary.  The CM arithmetic split of the
15 SSP primes over `Q(sqrt(-7))` is `5 split + 9 inert + 1 ramified`, while
the DASHI/Hecke atom grammar is `7 geometry/amplitude lanes + 7
phase/dynamics lanes + 1 sign/reaction-orientation lane`.  These are distinct
partitions.  The `p71` lane is split in the CM table and may only be used as
terminal SSP sign/carry/reaction-orientation bookkeeping, not as an inert
observer prime or a time theorem.  This boundary is checked by
`HeckeCarrierVsCMSplittingReceipt` and `P71HeckeMirrorSignLaneReceipt`.

## Non-Promoting Instantiations

### Navier-Stokes

NS reads the ratio as:

```text
theta(K,t) = |Flux_{>K}(u,t)| / Diss_{>K}(u,t)
```

The Agda links are:

- `NSTailFluxAbsorptionMarginReceipt`
- `NSTailFluxIdentityAnalyticTargetReceipt`
- `DashiCFDThetaRuntimeDiagnosticReceipt`

Paper 0 does not prove the fixed-`K` Littlewood-Paley identity, theta
preservation, BKM/Serrin continuation, or Navier-Stokes regularity.

### Yang-Mills

YM reads the ratio as:

```text
rho = actual same-prime Wilson polymer activity / KP-Balaban absorber
```

The Agda links are:

- `YMKPActivityRatioMarginReceipt`
- `YMKPAbsorptionMarginThresholdReceipt`
- `YMActualPolymerActivityDefinitionReceipt`
- `YMBalabanRGScaleTransferFrontierReceipt`

Paper 0 does not prove actual rho `< 1`, Balaban RG contraction, continuum
Yang-Mills, mass gap, or Clay Yang-Mills.

### Gate 3

Gate 3 reads the ratio as:

```text
q_N = projection defect at cutoff N / frame-Mosco recovery strength
```

The Agda links are:

- `Gate3NormDictionaryReceipt`
- `Gate3AdelicSobolevNormBindingReceipt`
- `Gate3MoscoRecoveryPreciseReceipt`
- `Gate3NoSpectralPollutionReceipt`
- `Gate3ScaleGraphBarrierInstantiationReceipt`
- `AtomExtendedCarrierFrameReceipt`
- `HeckeCarrierVsCMSplittingReceipt`
- `P71HeckeMirrorSignLaneReceipt`

Paper 0 records finite-cutoff norm/frame evidence and the exact continuum
obligations.  It does not prove PAWOTG density, Mosco recovery, no spectral
pollution, mass-shell transfer, or Gate 3 closure.

## Universal Barrier Target

The finishing theorem shape is recorded but not proved:

```text
scale graph node v:
  residual R_v
  production P_v
  absorption A_v
  ratio q_v = P_v / A_v

if physical projection is faithful,
   node dynamics obey the strict-margin grammar,
   edge transport is conservative or absorbable,
   danger-node absorbers dominate incoming transfer,
   and max_v q_v(0) < 1,
then max_v q_v(t) should not cross 1.
```

This is the `ScaleGraphBarrierTargetReceipt` and
`UniversalScaleGraphBarrierTargetReceipt` target, not a theorem proved in
Paper 0.

## Submission Boundary

Recommended submission framing:

- venue class: applied logic, formal methods in mathematical physics, or
  typed proof-interface note;
- primary contribution: fail-closed margin grammar plus checked promotion
  discipline;
- secondary contribution: one terminology/router table and three
  non-promoting physical instantiations;
- excluded claims: Clay, continuum YM, NS regularity, Gate 3 closure, terminal
  unification.

The exact current promotion fence is:

```text
nsRegularityPromoted = false
ymMassGapPromoted    = false
gate3Closed          = false
clayPromoted         = false
```

These fields are checked by
`Paper0SharedMarginGrammarConsolidationReceipt`.
