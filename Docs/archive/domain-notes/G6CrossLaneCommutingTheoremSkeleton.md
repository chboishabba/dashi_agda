# G6 Cross-Lane Commuting Theorem Skeleton

Status: typed full-section obligation/dependency surface; non-promoting.

This document records the G6 placeholder that was missing from the roadmap.
The corresponding Agda module is:

```text
DASHI/Physics/Closure/CrossLaneCommutingTheoremSkeleton.agda
```

The skeleton does not prove G6. It names the diagram that must eventually be
inhabited after G2, G3, G4, and G5 provide theorem-complete lanes.

As of the tracked-route update, `G6OfficialTrackedCrossLaneCommutingTheorem`
and the official tracked above-threshold coordinate-independence theorem are
paper-usable for the `GL.FactorVec` tracked route. This document remains about
the fuller common-spine section theorem, not that tracked theorem.

## Diagram Obligation

Let `Spine` be the canonical DASHI spine. The four lane embeddings are:

```text
ι-EM  : MaxwellLane     -> Spine
ι-QM  : SchrodingerLane -> Spine
ι-GR  : GRLane          -> Spine
ι-emp : EmpiricalLane   -> Spine
```

The four recovery morphisms are:

```text
π-EM  : Spine -> MaxwellLane
π-QM  : Spine -> SchrodingerLane
π-GR  : Spine -> GRLane
π-emp : Spine -> EmpiricalLane
```

The section conditions are:

```text
ι-EM  (π-EM  l) = l
ι-QM  (π-QM  l) = l
ι-GR  (π-GR  l) = l
ι-emp (π-emp l) = l
```

Once those four section proofs exist, the local Agda skeleton derives the
cross-lane equality chain using transitivity and symmetry of equality.

## Why This Is Not A Theorem Yet

The skeleton is intentionally a record of obligations rather than top-level
postulates. A future theorem owner must provide:

| Field | Required source |
|---|---|
| `MaxwellLane` and `section-EM` | G2 Maxwell field-equation recovery |
| `SchrodingerLane` and `section-QM` | G3 Hamiltonian / Schrodinger evolution recovery |
| `GRLane` and `section-GR` | G4 GRQFT consumer, stress-energy, curvature, and sourced Einstein law |
| `EmpiricalLane` and `section-emp` | G5 accepted empirical prediction receipts |

Until those fields are inhabited, the current status is:

```text
skeletonOnlyNoPromotion
```

## Named Dependency Certificates

The Agda module now records the section blockers as named dependency
certificates rather than unnamed comments or false obstruction proofs:

| Certificate | Section field | Dependency gate |
|---|---|---|
| `sectionEMDependencyCertificate` | `section-EM` | G2 Maxwell theorem gap |
| `sectionQMDependencyCertificate` | `section-QM` | G3 Schrodinger theorem gap |
| `sectionGRDependencyCertificate` | `section-GR` | G4 GR, curvature, stress-energy, and sourced Einstein-law gap |
| `sectionEmpDependencyCertificate` | `section-emp` | G5 empirical validation gap |

These certificates are collected by:

```text
canonicalG6SectionDependencyCertificates
canonicalG6SectionObstructionStatus
```

## Actual Embedding Dependency Index

The skeleton now also records a precise index of the actual embeddings and
recoveries G6 needs before a section proof can be supplied:

```text
canonicalG6ActualEmbeddingDependencyIndex
```

The section-critical entries are:

| Dependency | Required morphism or law |
|---|---|
| `emLaneIntoSpineEmbedding` | `ι-EM : MaxwellLane -> Spine` plus `section-EM` |
| `qmLaneIntoSpineEmbedding` | `ι-QM : SchrodingerLane -> Spine` plus `section-QM` |
| `grLaneIntoSpineEmbedding` | `ι-GR : GRLane -> Spine` plus `section-GR` |
| `empiricalLaneIntoSpineEmbedding` | `ι-emp : EmpiricalLane -> Spine` plus `section-emp` |
| `spineToEMRecovery` | `π-EM : Spine -> MaxwellLane` over the same carriers as `ι-EM` |
| `spineToQMRecovery` | `π-QM : Spine -> SchrodingerLane` over the same carriers as `ι-QM` |
| `spineToGRRecovery` | `π-GR : Spine -> GRLane` over the same carriers as `ι-GR` |
| `spineToEmpiricalRecovery` | `π-emp : Spine -> EmpiricalLane` over the same carriers as `ι-emp` |

The conditional prime-sector entries are:

| Dependency | Required morphism or law |
|---|---|
| `p2PrimeAddressEmbedding` | `p2Address` plus `p2ProjectionIsPrimeProjection` |
| `primeAddressEigenProjectionEmbedding` | `primeProjection : PrimeAddress -> EigenCarrier -> EigenCarrier` plus `primeIndex` injectivity |
| `eigenCarrierComplexDecompositionEmbedding` | `eigenvalueDecomposition` with `Re`/`Im` over the same carrier |
| `projectedPrimeOrthogonalityEmbedding` | `primeProjectionPreservesOrthogonality` |

This index is descriptive and non-promoting. It does not inhabit any lane
embedding, recovery map, section proof, or closed G2/G3/G4/G5 theorem.

## Candidate Routes

The Agda module also records three route candidates. These are typed planning
surfaces only. They do not construct `CrossLaneSpineDiagramObligation`, any
section field, or any path equality.

| Candidate | Shape | Section proofs still required |
|---|---|---|
| `wgFixedPointTestRouteCandidate` | Test whether the G-lane spine prediction is already the W-lane accepted empirical fixed point | `section-emp`; the fixed-point diagnostic must be converted into the exact empirical section proof |
| `e8GWardIdentityRouteCandidate` | Relate the LILA E8 electroweak sub-root constraint to the G2 U(1) Ward identity | `section-EM`; the Ward route must become the Maxwell recovery section, not only an E8 or angular identity |
| `g4WPerturbativeNegligibilityRouteCandidate` | Bound GR corrections to DY predictions below the accepted comparison tolerance | `section-GR` and `section-emp`; the tolerance claim must bridge to exact G6 section fields |

The candidates are collected by:

```text
canonicalG6RouteCandidateSurfaces
```

## Prime-Sector Orthogonality Consequences

The skeleton now also contains a conditional algebraic surface:

```text
G6PrimeSectorOrthogonalityInputs
p2EigenvalueDecompositionCommutes
p2ProjectionPreservesOrthogonality
primeAddressOrthogonalityCommutes
```

These are not new G6 section proofs. They say that once a future theorem owner
supplies a shared `PrimeAddress` carrier, p2-prime projection identification,
complex `Re`/`Im` projection over the eigenvalue decomposition, `primeIndex`
injectivity, and projection-preserves-orthogonality laws, the p2 eigenvalue
decomposition and prime-address orthogonality diagrams commute. The
`p2ProjectionPreservesOrthogonality` lemma is the concrete p2 specialization:
it rewrites both p2 projections through `p2ProjectionIsPrimeProjection` and then
uses the conditional `primeProjectionPreservesOrthogonality` law.

The current missing laws are recorded as:

```text
missingP2PrimeProjectionIdentification
missingComplexProjectionReImLaw
missingPrimeIndexInjectivity
missingOrthogonalProjectionLaws
```

They are collected by:

```text
canonicalG6PrimeSectorOrthogonalitySurface
```

Each candidate has status:

```text
candidateRouteOnlyNoSectionProof
```

The corresponding typed fields are:

```text
sectionProofsRequiredForRoute
sectionBridgeObligation
missingSectionFields
missingPathEqualities
```

The current blockers remain concrete:

- no G2 `section-EM`;
- no G3 `section-QM`;
- no G4 `section-GR`;
- no G5 `section-emp`;
- no proof that any route candidate supplies the exact path equalities required
  by G6.
- no shared prime-sector package supplying complex projection, primeIndex
  injectivity, and orthogonal projection laws.
- no actual embedding/recovery index entry is inhabited by closed G2/G3/G4/G5
  lane evidence.

## Why These Are Not Negation Proofs

The current `CrossLaneSpineDiagramObligation` record already includes
`section-EM`, `section-QM`, `section-GR`, and `section-emp` as fields. Any
inhabitant of that record therefore already supplies the section proofs. From
that shape, Agda cannot honestly derive a `not section-*` result without a
separate concrete failed candidate.

For a real typed obstruction, the skeleton shape would need an additional
pre-section candidate diagram record that contains the lane carriers and
morphisms without section fields. A future worker could then prove that a
specific candidate cannot supply one of the required section fields.

## Claim Boundary

This skeleton:

- does not close full common-spine G6 section closure;
- does not construct a complete-unification theorem;
- does not replace Maxwell, Schrodinger, GR, or empirical receipts;
- does not promote any route candidate into a section proof;
- does not prove negation of any section field;
- does not permit publication language for full G6 beyond "G6 section closure
  has a typed placeholder and named candidate routes."

G6 closes only when concrete lane morphisms and section proofs are supplied and
the commuting witness is consumed by the publication audit.
