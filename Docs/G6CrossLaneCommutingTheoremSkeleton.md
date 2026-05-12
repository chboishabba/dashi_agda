# G6 Cross-Lane Commuting Theorem Skeleton

Status: typed obligation surface; non-promoting.

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

## Claim Boundary

This skeleton:

- does not close G6;
- does not construct a complete-unification theorem;
- does not replace Maxwell, Schrodinger, GR, or empirical receipts;
- does not permit publication language beyond "G6 obligation has a typed
  placeholder."

G6 closes only when concrete lane morphisms and section proofs are supplied and
the commuting witness is consumed by the publication audit.
