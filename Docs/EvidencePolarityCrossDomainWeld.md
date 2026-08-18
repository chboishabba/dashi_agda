# Claim-indexed evidence polarity across PNF, hyperfabric, biology and atomics

This tranche is a cross-pollination weld over existing DASHI carriers. It does not introduce a new four-valued logic, a second authority algebra, a replacement PNF, or a parallel chemistry/biology proof system.

## Shared evidence shape

DASHI already has `DASHI.Algebra.DisagreementFourViewBoundary.PolarAssessment`:

```text
(supports P, supports not-P) : Bool x Bool
```

The four informational states remain distinct before any lossy presentation:

```text
(true,false)  positive-only
(false,true)  negative-only
(true,true)   conflict / both
(false,false) missing / neither
```

`ClaimIndexedEvidencePolarityExact` adds one missing typing discipline: evidence is pooled only inside a common claim/context fibre. Evidence about a different claim, body, time, place, relation, institution, observer, or provenance scope requires an explicit alignment witness before pooling.

This prevents axis/context collapse from manufacturing contradiction.

Logical/informational calibration:

- Nuel D. Belnap, "A Useful Four-Valued Logic", in J. Michael Dunn and George Epstein (eds.), *Modern Uses of Multiple-Valued Logic* (1977), DOI `10.1007/978-94-010-1161-7_2`.
- J. Michael Dunn, "Intuitive Semantics for First-Degree Entailments and 'Coupled Trees'", *Philosophical Studies* 29(3), 149-168 (1976), DOI `10.1007/BF00373152`.

Those sources motivate independent positive/negative information coordinates. Claim/context-indexed pooling is a DASHI-local typing rule.

## Required-axis completeness remains a separate layer

Incoming PR #582 independently contains `DASHI.Core.RequiredAxisSupportSquareExact`, including `AxisEvidenceFamily`, `RequiredAxesResolved`, `MissingRequiredAxis`, `ConflictingRequiredAxis`, and the theorem that positive evidence on another axis cannot fill a missing required axis.

This tranche does not duplicate that calculus. On stack convergence, `RequiredAxesResolved` is the natural proof-bearing producer for the coarse `obligationsDischarged` status used here.

So the intended product is:

```text
claim/context-indexed evidence
x required-axis completeness
x existing authority gate
```

rather than any one coordinate standing in for the others.

## Existing authority gates are reused

`EvidenceObligationAuthoritySeparationExact` reuses `DASHI.Promotion.AuthorityGateCore`.

A positively supported claim may still have open technical obligations. Even after technical obligations are discharged, the canonical local authority gate remains closed until the relevant external/domain authority bridge is supplied.

Thus:

```text
support != obligation discharge
obligation discharge != authority
conflict != affirmative promotion
authority cannot be manufactured from local formal evidence
```

The existing `CrossDomainClaimPromotionBoundary`, `ObligationIndex`, and domain authority-intake modules remain authoritative for their own promotion lanes.

## Dialectic and 369

`DialecticInvariantGeometry.DialecticField` already supplies two independent predicates: thesis and antithesis. Pointwise this has exactly the support-square shape.

`ClaimEvidence369BridgeExact` exposes that correspondence but keeps the 369/TriTruth presentation coarser. `TetralemmaBridge.triResidual` can produce `exact`, `partial`, or `noTypedMeet` and already proves that it cannot produce the explicit `contradiction` residual.

Therefore:

```text
fine support/refutation evidence -> optional ternary/369 presentation
```

not:

```text
369 presentation = complete evidence state.
```

Likewise `EvidenceHorizon369` already carries fine signed evidence and proves that omitted horizon evidence is not refutation. The support square is a qualitative summary, not a replacement for the signed coordinate.

## Hyperfabric and hypervoxel

`TypedHyperfabricCore` already provides stalks, restriction maps, compatible global sections, provenance and obstructions. Claim-indexed evidence can therefore live locally in typed stalks without changing the hyperfabric semantics.

`RecursiveRadixHypervoxel` gives a particularly exact geometric witness: the lifted carrier has a ternary base plus a polarity fibre, and `centralFlip` changes the fine polarity while leaving the projected base address unchanged.

This is a source-native example of vertical fine motion invisible at the coarse base.

Centre-blind descent continues to require the existing invariance proof; polarity is not promoted into another ternary geometric axis.

The hyperfabric source already recorded in the core is:

- Iulia Duta, Giulia Cassarà, Fabrizio Silvestri and Pietro Liò, "Sheaf Hypergraph Networks", arXiv:2309.17116, DOI `10.48550/arXiv.2309.17116`.

No empirical neural-network performance claim is imported by this tranche.

## Intersectional carrier

`IntersectionalLongitudinalResidualDynamics` keeps the situated carrier explicit as:

```text
body x time x place x relation x institution x axis-bundle.
```

`IntersectionalClaimEvidenceFibreExact` uses that entire value as the evidence context index. Consequently two situated evidence packets cannot be pooled merely because their surface labels look similar. An explicit equality/alignment witness is required first.

This preserves the existing no-axis-neutral-universalism boundary.

## Trauma, memory and learning

`MemoryFibre` and `LearningAlgebra` already prove that revaluation, habituation, extinction and phase realignment can preserve remembered-event identity.

`MemoryEvidencePolarityLearningBridgeExact` makes evidence appraisal orthogonal to that preserved memory identity:

```text
before evidence polarity -> after evidence polarity
```

may change while the remembered PNF event remains the same.

Thus revision/counterevidence need not mean memory deletion, and extinction remains action-dominance inhibition rather than semantic erasure.

The existing `TraumaMemoryHypervoxelBridge` continues to own trauma/body-memory placement and explicitly blocks residuals from becoming diagnoses.

## Brain and biological proxies

`BrainProxyEvidenceAuthorityBridgeExact` reuses `FMRIConnectomeProxyGovernance`, `BrainDNABodyMemoryBridge`, and the canonical clinical authority gate.

A positive BOLD/connectome/representation observation can occupy an evidence coordinate while hidden-state recovery, trauma proof, diagnosis, treatment and clinical authority remain blocked.

So:

```text
proxy evidence != hidden state
proxy evidence != diagnosis
representation != trauma proof
```

## Chemistry

`EvidenceObligationAuthorityBridgeExact` reuses:

- `ChemistryQuantitativeAdapter` for exact-reference, measurement, preservation, protocol and replication obligations;
- `ChemistryAuthorityBinding` for NIST ASD, NIST Chemistry WebBook and CODATA authority-token shapes;
- `AuthorityGateCore` for fail-closed scientific authority;
- `NeurochemicalAtomicChemistryBridge` for candidate-only molecular/kinetic semantics and clinical non-promotion.

Thus even positive candidate evidence plus completed local technical work does not silently create scientific or clinical authority.

## Physical atomics versus dialectical atom bookkeeping

`AtomicEvidenceObligationBridgeExact` preserves the strongest naming boundary in this tranche.

`AtomicPeriodicTableRecoveryBoundary` is a physical theorem boundary requiring independent witnesses for force sectors, orbital control, shell recurrence, fermionic lift, interacting minima, shell dictionary and valence projection.

`DialecticalAtomFrontierReceipt` is explicitly bookkeeping vocabulary: 7+7+1 lanes, balanced-trit/carry notation, signed-zero torsion markers, pressure/anisotropy bookkeeping, braid/discourse trajectories and tetration markers. Its own promotion surface blocks physical/Clay conclusions.

Therefore:

```text
dialectical atom != physical atom
bookkeeping evidence != periodic-table recovery witness.
```

## Shared anti-collapse spine

The resulting cross-domain invariant is:

```text
fine claim/context fibre
-> positive/negative evidence with provenance
-> required-axis completeness when needed
-> domain proof obligations
-> existing authority gate
-> governed projection / action.
```

with the explicit non-identifications:

```text
conflict != ignorance
omission != refutation
cross-context evidence != same-claim contradiction
support != obligation discharge
obligation discharge != authority
coarse presentation != fine state
learning/reweighting != erasure
proxy observation != diagnosis
physical theorem witness != symbolic bookkeeping analogy.
```

## Validation boundary

This tranche is source/API/proof-shape reviewed against the live repository. The current connector runtime does not expose a usable Agda 2.9 executable, so no fresh kernel-clean claim is made here. No GitHub Actions, CI or CodeRabbit are invoked by this tranche.
