# Navier–Stokes Paper 1 Modern Proof-Spine Migration Design

Date: 2026-09-13
Branch: `agent/ns-paper-modern-proof-spine-design`
Status: approved architecture; design/spec only; no manuscript or theorem-interface implementation yet

## Purpose

Migrate Paper 1 from the June A1–A9 ESS/Abel-defect reduction architecture to the modern proof-critical Navier–Stokes spine already present in `DASHI/Physics/Closure`, while preserving the A1–A9 route transparently as historical/alternative provenance.

The migration must not promote any open analytic leaf to theorem status. In particular, the live paper remains conditional until the actual modern producer chain closes. The modern paper surface must distinguish:

- mathematical theorem/proof status;
- statement/interface status;
- certification status;
- historical/provenance routes;
- negative controls and superseded routes.

## Current mismatch

The live manuscript `Docs/papers/live/Paper1NavierStokesClayDraft.md` is still organized around the June A1–A9 tail-flux/ESS/Abel-defect route and names A1/A3 and A4 as its principal mathematical frontiers.

The paper-facing formal interface `DASHI/Papers/NavierStokes/TheoremInterface.agda` is likewise stale: it is centered on the A6–A9 and Round62-era Com/Schur frontier rather than the later same-object/direct-companion construction.

The modern proof archaeology instead identifies the live critical chain as approximately

```text
literal periodic Galerkin NS
  -> signed/helical commutator geometry
  -> same-output residual / direct companion construction
  -> literal R406 remainder
  -> CommutatorOnlySpacetimeBudget568
  -> DirectLeafACompilerRound572
  -> DirectOffDiagonalBudget (R503)
  -> critical-barrier consumer
```

with exact same-object remainder lineage through the R104/R406 and direct-companion owners.

## Design principle

Paper 1 must follow the causal proof spine, not historical round numbering.

Historical material stays visible. Earlier routes are never silently deleted or rewritten as if they did not happen. Each superseded route should be retained with an explicit account of:

- what it was trying to prove;
- what theorem-bearing work it contributed;
- which later result superseded or bypassed it;
- why it was not ultimately used as the primary producer;
- whether it remains a useful donor, negative control, or alternative route.

## New paper architecture

### 1. Main theorem, claim boundary, and live cutset

Lead with the current conditional theorem surface rather than A1–A9.

Primary live hypothesis:

```text
DASHI/Physics/Closure/NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact.agda
  CommutatorOnlySpacetimeBudget568
```

Paper statement: the downstream compiler chain is constructed, while the cutoff-uniform spacetime producer remains the live analytic frontier unless and until a source-written producer and certification receipt close it.

The paper must explicitly avoid an unconditional Clay/global-regularity claim while this hypothesis is open.

### 2. Literal periodic finite-dimensional carrier

Describe the exact periodic Galerkin carrier, Fourier modes, physical triad incidence, Leray/helical decomposition, and exact dynamics needed by the modern chain.

Representative owners include the existing periodic Fourier/helical and physical-incidence modules used by R571/R574 and the R406/direct-companion line.

This section should distinguish exact finite algebra from continuum/imported analytic authority.

### 3. Signed commutator and helical construction

Present the cancellation-preserving construction before norm majorization:

- pure multiplier-difference / commutator lineage;
- exact helical decomposition;
- fixed-helicity multiplier-difference cells;
- raw directional kernel realization;
- low-output local estimates.

Representative modern owners:

```text
NSTriadKNInnerHelicalComponentCommutatorRound571Exact.agda
NSTriadKNFourHelicityComponentMassCollapseRound575Exact.agda
```

and the surrounding R573/R574 owners.

Historical donors to retain in a provenance box/appendix:

- July signed multiplier-difference commutator lane;
- early-August centered first/second-moment machinery;
- six-three gap arithmetic;
- R127/R128 radial/square-gap/Plücker geometry;
- R172–R178 raw-curl dual-defect and low-output estimates.

### 4. Same-output Gram/covariance obstruction

Explain the exact residual after partner/block compression rather than using a generic “Gram problem” label.

Canonical historical owner chain:

```text
R179/R180 : exact polarization + Gram ledger
R181      : partner-first compression
R201      : law of total Gram / covariance
R205      : literal localized comparable partner cells
R206      : exact localized compressed Gram frontier
R207      : same-output carrier
R208      : outer Fourier L2 carrier
R209      : outputwise Gram telescope
R211      : quantitative residual-payment consumer socket
R214      : constant-band localization no-go / negative control
```

The manuscript must state that localization alone does not pay same-output covariance; R214 is a negative control, not a failure of the whole signed/resolvent route.

PR #890’s compressed partner-difference/PSD adapter belongs here as an active construction experiment, not as a completed producer unless its physical separation theorem and certification close.

### 5. P3 separation producer frontier

State the actual local proof-search target clearly.

For fixed-output compressed partner cells `B_alpha`, seek a quantitative anti-alignment/separation theorem. The useful complete-graph identity is

```text
Debt = (n-1) * sum ||B_alpha||^2
       - sum_{alpha<beta} ||B_alpha - B_beta||^2.
```

The producer problem is therefore to obtain enough physical lower control on pairwise difference energy to pay the same-output debt.

Potential donor geometry should be kept ordered by proof value:

1. exact raw-curl/BAC–CAB algebra;
2. magnitude/direction separation;
3. R127/R128 radial + Plücker geometry;
4. R176 dual-defect geometry;
5. centered/Taylor/second-moment machinery;
6. six-three scale aggregation.

This section must not claim that a local single-cell R176 estimate automatically controls arbitrary inter-partner differences.

### 6. Weighted/nested commutator and full-square normal form

Describe the route from exact signed cells to the modern weighted commutator/full-square carrier while preserving cancellation before positive envelopes.

Representative owners include:

```text
R294 weighted mixed commutator
R545 spectator factorization
R567 literal forcing full square
R568 live commutator-only spacetime budget
```

The manuscript should explain that R575/R576/R577 provide valid positive/Gram fallback reductions but are not automatically the highest-alpha centered-cancellation producer.

### 7. Direct companion and literal R406 same-object lineage

Make the modern same-object remainder genealogy central.

Representative owners:

```text
NSTriadKNRound104ToLiteralR406CriticalSliceRound507Exact.agda
NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact.agda
NSTriadKNDirectResolventIntegratedCompanionRound500Exact.agda
NSTriadKNDirectResolventSignedCrossToR415Round503Exact.agda
```

The paper should expose the exact identity chain used by the live consumer rather than describing `C_direct` as missing. The direct companion is constructed; its uniform analytic producer is what remains open.

### 8. Terminal compiler chain

Document that the downstream compiler is already present:

```text
CommutatorOnlySpacetimeBudget568
  -> NSTriadKNDirectLeafACompilerRound572Exact
  -> R503.DirectOffDiagonalBudget
  -> existing critical-barrier consumer
```

R572 must be described as a compiler, not as an independent PDE producer.

Nested Schur/R577 remains a fallback compiler route and should be marked as such.

### 9. Certification and claim-status appendix

Every proof-critical owner cited by the paper gets a four-column status row:

```text
owner | role | MathematicalStatus | StatementStatus | CertificationStatus
```

`CertificationStatus` is split into:

```text
validation root exists?
workflow targets it?
observed commit-specific Agda success receipt?
```

A workflow target without a recovered successful run is not promoted to kernel-certified status.

The R101–R214 archaeology and later R4xx/R5xx owners should be represented at proof-critical resolution rather than by enumerating every historical round.

## Historical A1–A9 treatment

The current June manuscript is not deleted or covered up.

Its A1–A9 route moves to a clearly labeled historical/alternative-strategy appendix, preserving:

- the original theorem statement and date/version context;
- ESS/Abel-defect motivation;
- A1/A3 and A4 unresolved frontiers;
- any theorem-bearing infrastructure that later fed the modern proof;
- explicit reason it was superseded as the primary manuscript route: it does not match the current shortest same-object/direct-companion proof spine.

The appendix should say that this was a serious earlier reduction attempt, not a fabricated strawman, and should identify which parts remain useful as diagnostics or alternative reductions.

## Formal interface migration

`DASHI/Papers/NavierStokes/TheoremInterface.agda` should be replaced in place rather than accompanied by a second parallel paper interface.

The new interface should expose three families of fields:

### Modern canonical spine

- literal R406/same-object remainder lineage;
- direct companion constructed;
- R568 live producer status;
- R572 compiler status;
- R503 direct-off-diagonal consumer status;
- current Clay/terminal promotion guards.

### Current proof-search frontier

- same-output debt identity/consumer;
- P3 separation producer status;
- modern centered-cancellation transplant status if/when constructed;
- explicit open fields rather than optimistic booleans.

### Historical provenance

- A1–A9 historical route retained as `historicalAlternativeRoute`-style metadata/status;
- Round62-era Com/Schur interface retained as predecessor/superseded-route metadata where still useful;
- no historical proof/status is rewritten as if it never existed.

## Paper-to-owner mapping

Initial mapping for implementation:

| Paper section | Primary formal owners |
| --- | --- |
| Main live cutset | `NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact` |
| Modern direct compiler | `NSTriadKNDirectLeafACompilerRound572Exact` |
| Direct downstream budget | `NSTriadKNDirectResolventSignedCrossToR415Round503Exact` |
| R104/R406 same-object weld | `NSTriadKNRound104ToLiteralR406CriticalSliceRound507Exact`, `NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact` |
| Direct companion | `NSTriadKNDirectResolventIntegratedCompanionRound500Exact` plus R496–R503 lineage |
| Helical multiplier difference | `NSTriadKNInnerHelicalComponentCommutatorRound571Exact` and R573/R574 neighbours |
| Four-channel scalar fallback | R575/R576/R577 modern owners |
| Historical Gram/block obstruction | R179/R180/R181/R201/R205–R214 owners |
| Historical centered donor | Luo centered paired-commutator / second-moment / physical centered assembly owners |
| Historical A1–A9 route | current Paper 1 + existing A6–A9 theorem-boundary modules |

This table is a starting map; implementation should resolve exact filenames for every R-numbered citation before final prose is merged.

## Files to change during implementation

Primary:

```text
Docs/papers/live/Paper1NavierStokesClayDraft.md
DASHI/Papers/NavierStokes/TheoremInterface.agda
```

Likely secondary synchronization:

```text
Docs/papers/PublicationRoadmap.md
Docs/roadmaps/ClayNSProofRoadmap.md
Docs/support/reference/NSAnalyticState.md
Docs/support/reference/AgdaValidationTargets.md
Docs/papers/README.md (only if status wording requires it)
publication/readiness tests or manifests that assert current Paper 1 status text
```

Do not create a second live NS manuscript or a second theorem interface.

## Verification strategy

Implementation must use the existing repo validation architecture.

At minimum:

1. source-level paper/interface consistency checks;
2. publication-readiness tests/manifests;
3. focused Agda validation root for the migrated theorem interface;
4. existing pinned Agda workflow where applicable;
5. explicit distinction between workflow wiring and an observed successful run.

No claim of kernel certification without an actual receipt tied to the implementation head.

## Success criteria

The migration is successful when:

1. Paper 1’s main narrative follows the modern proof spine rather than A1–A9.
2. A1–A9 remains available and honestly described as historical/alternative provenance.
3. The paper-facing theorem interface names the modern live owner chain and fail-closes all open producers.
4. `C_direct` is described as constructed; R568 is described as the live producer leaf.
5. R572/R503 are classified as downstream compiler/consumer surfaces, not producers.
6. P3/same-output debt is represented as the current local proof-search frontier without claiming completion.
7. MathematicalStatus, StatementStatus, and CertificationStatus remain distinct.
8. No unconditional Clay/global-regularity claim appears unless the corresponding proof and certification state actually changes.

## Non-goals

This migration does not itself prove P3, R568, global regularity, or the Clay statement.

It does not erase older routes.

It does not add a new generic Fourier/Gram framework.

It does not create a second paper interface.

It does not treat workflow configuration as a kernel receipt.
