# YM / Unification Paper-to-Proof Map

Status: live theorem-navigation document. This file maps the two live manuscripts to exact formal owners and separates compiler closure from missing mathematical input.

Primary manuscripts:

- `Docs/papers/live/Paper3YangMillsClayDraft.md`
- `Docs/papers/live/Paper8UnificationDraft.md`

Implementation plan:

- `docs/superpowers/plans/2026-09-12-ym-unification-full-proof-spines.md`

## Paper 3 — Yang–Mills

### Manuscript Theorem 1.1

Paper statement: finite self-adjointness + uniform finite spectral margin + continuum transfer + RP/OS reconstruction imply positive continuum mass gap.

Formal surfaces:

- typed paper proof spine: `DASHI/Physics/Closure/YMPaper3ContinuumTransferProofSpineExact.agda`
- legacy authority/status surface: `DASHI/Physics/Closure/YMContinuumMassGapTransferAuthority.agda`
- operator-continuum audit: `DASHI/Physics/YangMills/YMOperatorDomainContinuumFrontier2026Exact.agda`

Current status:

- composition of supplied theorem-bearing H3a/H3b/no-pollution/OS witnesses into a positive-gap conclusion: **compiler-owned** in the new typed spine;
- actual physical H3a producer: **open**;
- actual H3b limiting-vacuum continuity: **open**;
- actual physical OS/Wightman package / same-evolution identification: **open**;
- Clay promotion: **not claimed**.

### Manuscript Theorem 5.1 — continuum-transfer interface

Paper chain:

```text
H3a trace/norm-resolvent transfer
  -> H3b vacuum-projection continuity
  -> no spectral pollution below m_*
  -> continuum positive spectral margin.
```

Typed owner:

- `YMPaper3ContinuumTransferProofSpineExact.Paper3ContinuumTransferSpine`

Important generic donors already proved in-repo:

- `BalabanVacuumOrthogonalMoscoRecoveryExact.physicalVacuumGapAfterRecovery`
- `BalabanClayDenseCoreSpectralGapExact.denseLocalClusteringImpliesGap`

These are **generic compilers**, not physical-YM producers.

### Shorter recovery-gap sufficient route

Formal owner:

- `DASHI/Physics/Closure/YMPaper3VacuumRecoveryGapProofAdapterExact.agda`

Exact theorem reuse:

```text
VacuumOrthogonalRecoverySystem
  -> PhysicalVacuumGapAfterRecovery
```

from `BalabanVacuumOrthogonalMoscoRecoveryExact`.

This route is not asserted identical to Paper 3's stronger trace-norm H3a theorem. It is a sufficient lower-gap-survival route. Its first real missing physical object is therefore:

```text
physical Yang–Mills VacuumOrthogonalRecoverySystem
```

with the exact finite/limit vectors, vacuum-orthogonality witnesses, norm domination, uniform finite gap, and recovery-energy upper bound.

The older Sprint121/128/129 carrier/recovery/no-pollution files are **receipt ledgers**, not theorem-bearing producers of this record: they store strings and Boolean closure/status evidence but do not supply the finite/limit vector maps, norms, energies, recovery vector, or vacuum-orthogonality proofs required by `VacuumOrthogonalRecoverySystem`.

### Row-C clustering -> dense-core spectral exclusion route

Formal owner:

- `DASHI/Physics/Closure/YMPaper3RowCToDenseCoreGapAdapterExact.agda`

Existing theorem-bearing ingredients:

```text
BalabanRowCPostBC2PhysicalCompletionRound108Exact
  : UniformGeometricConnectedClustering Observable

BalabanClayDenseCoreSpectralGapExact
  : UniformDenseCoreClustering dataSet
      -> DenseCoreSpectralExclusion dataSet
```

The adapter isolates the exact same-object continuum payment:

```text
dense centered core vector
  -> corresponding Row-C observable
  -> literal Row-C geometric clustering theorem
  -> exact CoreClusteringEstimate for the OS/Hilbert dense-core consumer.
```

Once `RowCToDenseCoreClusteringWeld` and the physical `DenseCoreProjectionData` exist, spectral exclusion and the positive dense-core gap are compiler output.

This is presently the strongest bridge between the modern CMP119/CMP116/Row-C work and Paper 3's continuum spectral theorem. It does **not** identify the finite/local Row-C observable carrier with the continuum OS/Wightman dense core by fiat.

### Manuscript Theorem 5.2 — H3a from constructive RG inputs

Paper statement: Balaban multiscale fluctuation-integral control + large/small-field decomposition + polymer activity decay + Casimir suppression produce trace-norm transfer convergence on the vacuum-orthogonal sector.

Current formal status:

- source/RG pieces exist across the Balaban source-native and polymer lanes;
- the full physical theorem mapping those objects to the exact H3a transfer/norm-resolvent witness is **not yet constructed**;
- citation metadata alone does not inhabit H3a.

Recommended proof direction:

1. pursue the Row-C -> dense-core same-object weld because both theorem endpoints are already typed and this can turn physical clustering into an actual spectral-exclusion theorem;
2. in parallel construct the physical recovery-system producer, because the lower-gap transfer algebra is already closed;
3. retain full trace-norm H3a as the stronger Paper-3 route and prove it separately if the manuscript requires that exact strength;
4. do not substitute Mosco liminf, sprint receipts, or status Booleans for norm-resolvent/no-pollution theorems.

## Paper 8 — Unification / closure grammar

### U-1a / U-1a-H

Paper claim: quotient by the null class, recover JvN inner product after parallelogram, complete, then attach bounded consumers.

Existing formal owner:

- `DASHI/Physics/Closure/GluingOperatorLinearityOnDefectQuotientBoundary.agda`

Paper-facing live analytic wall is not JvN itself. It is UCT.1–UCT.4.

### UCT.1–UCT.4 typed proof spine

New formal owner:

- `DASHI/Physics/Closure/UnificationUCTFullProofSpineExact.agda`

Exact chain:

```text
UCT.1 ResidualPDE(actualU1aCrossTerm)
  -> UCT.2 OperatorClass
  -> UCT.3 UniqueContinuationAdmissible
  -> UCT.4 nullClass(actualU1aCrossTerm)
```

The compiler constructs the repository's existing
`U1aCrossTermNullityTheoremTarget` only from a genuine UCT.4 theorem.

Current status:

- UCT.1 exact lane-specific overlap residual PDE: **open**;
- UCT.2 elliptic/parabolic class: **open**;
- UCT.3 matched Carleman/unique-continuation theorem: **open**;
- UCT.4 cross-term nullity: **compiler target present, physical theorem open**.

No concrete in-repo UCT.1 PDE producer was located by exact/semantic search; the current repo contains the target/agenda but not the theorem. `UnificationCrossTermNullityDiscriminantBoundary` explicitly classifies the discriminant/Cauchy-Schwarz route as seed evidence only, not UCT.1 payment.

### UCT.4 -> UCT.5 typed transport

New formal owner:

- `DASHI/Physics/Closure/UnificationUCT4ToModuloNullLinearityExact.agda`

The actual proof chain now has a theorem-bearing compiler:

```text
UCT.4 nullClass(actual cross term)
  + nullClass x -> moduloNullEqual x zeroV
  + representative / G invariance
  + zero residual -> modulo-additivity transport
  -> UCT.5 G(s1+s2) = Gs1 + Gs2 modulo null.
```

The UCT.5 conclusion is genuinely derived once the quotient-semantics inputs are supplied. The missing quotient semantics are not represented as status Booleans in the new path.

### UCT.4 -> UCT.5 is not automatic

Existing boundary owner:

- `DASHI/Physics/Closure/UnificationNullToQuotientEqualityTransportBoundary.agda`

The full proof still needs:

1. `nullClass x -> moduloNullEqual x zeroV`;
2. representative invariance of nullity/equality;
3. congruence of quotient equality under `+V`, additive inverse and scalar action;
4. congruence under `G`;
5. transport of cross-term nullity into `G(s1+s2)=G(s1)+G(s2)` modulo null.

Only after these are proved does the existing four-point -> parallelogram -> JvN consumer chain become eligible.

### UCT.5–UCT.8

Current intended order:

```text
UCT.4 cross-term nullity
  -> null-to-quotient equality transport
  -> UCT.5 modulo-null G-linearity
  -> UCT.6 four-point cancellation
  -> UCT.7 parallelogram
  -> UCT.8 Jordan-von Neumann recovery
```

Existing boundary modules record these consumers, but the theorem-bearing null/equality and congruence bridges remain open.

## Current Pareto proof frontier

### YM

Non-dominated same-object producer:

```text
Row-C UniformGeometricConnectedClustering
  -> OS/Wightman dense centered core clustering estimate
```

because both sides already have theorem-bearing carriers and the downstream dense-core spectral-exclusion theorem is closed.

Parallel non-dominated physical producer:

```text
physical VacuumOrthogonalRecoverySystem
```

because the generic recovery-gap theorem is already explicit and immediately yields a continuum lower-gap inequality.

Parallel stronger route:

```text
physical H3a trace/norm-resolvent transfer witness
```

needed if Paper 3 is to retain Theorem 5.2 at its stated strength.

### Unification

Non-dominated analytic producer:

```text
UCT.1 exact overlap residual PDE
```

No in-repo inhabitant has been found. Until that PDE is fixed, UCT.2–UCT.4 cannot be honestly proved.

Nonanalytic downstream proof work now typed:

```text
nullClass x -> quotient equality with zero
+ representative/congruence theorems
-> UCT.5 modulo-null additivity.
```

This can be developed independently of the missing Carleman analysis and is immediately consumed once UCT.4 lands.

## Validation boundary

The new proof spines and adapters are source-level implementations on the active archaeology branch. They do not become kernel-verified merely by existing in GitHub. Exact-head Agda validation must be observed before changing certification status.
