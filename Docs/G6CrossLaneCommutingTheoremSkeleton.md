# G6 Cross-Lane Commuting Theorem Skeleton

Status: typed obligation/dependency surface; non-promoting.

This document records the G6 placeholder that was missing from the roadmap.
The corresponding Agda module is:

```text
DASHI/Physics/Closure/CrossLaneCommutingTheoremSkeleton.agda
```

The skeleton does not prove G6. It names the diagram that must eventually be
inhabited after G2, G3, G4, and G5 provide theorem-complete lanes.

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

- does not close G6;
- does not construct a complete-unification theorem;
- does not replace Maxwell, Schrodinger, GR, or empirical receipts;
- does not prove negation of any section field;
- does not permit publication language beyond "G6 obligation has a typed
  placeholder."

G6 closes only when concrete lane morphisms and section proofs are supplied and
the commuting witness is consumed by the publication audit.
