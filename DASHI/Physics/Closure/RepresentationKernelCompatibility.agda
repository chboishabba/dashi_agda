module DASHI.Physics.Closure.RepresentationKernelCompatibility where

-- Cross-pollination of the description-change question with the existing
-- refinement/kernel spine.
--
-- The stronger DASHI question is not merely whether a compressed description
-- preserves one scalar.  It is whether changing representation preserves the
-- dynamics:
--
--       fine state --fineStep--> fine state
--           |                       |
--        project                 project
--           |                       |
--           v                       v
--       coarse state --coarseStep-> coarse state
--
-- Exact compatibility says this square commutes on admissible states.
-- Approximate compatibility replaces equality by an explicitly named
-- equivalence/defect relation.  MDL may select a representative only after
-- this law-preserving relation has been supplied; shortness alone does not
-- establish physical equivalence.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level; lsuc; Setω)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

------------------------------------------------------------------------
-- Exact representation/kernel compatibility.

record RepresentationKernelCompatibility {ℓ : Level} : Set (lsuc ℓ) where
  field
    FineState : Set ℓ
    CoarseState : Set ℓ
    Observable : Set ℓ

    fineStep : FineState → FineState
    coarseStep : CoarseState → CoarseState
    project : FineState → CoarseState

    fineAdmissible : FineState → Set ℓ
    coarseAdmissible : CoarseState → Set ℓ

    fineObserve : FineState → Observable
    coarseObserve : CoarseState → Observable

    projectPreservesAdmissibility :
      ∀ {x} → fineAdmissible x → coarseAdmissible (project x)

    projectPreservesObservable :
      ∀ x → coarseObserve (project x) ≡ fineObserve x

    kernelCommutesWithProjection :
      ∀ {x} →
      fineAdmissible x →
      project (fineStep x) ≡ coarseStep (project x)

------------------------------------------------------------------------
-- A fixed point/attractor at the fine representation projects to a fixed
-- point at the coarse representation whenever the compatibility square
-- commutes.  This is the elementary theorem behind the stronger "shape"
-- reading: representation change preserves a dynamical object, not just a
-- number attached to a state.

projectedFixedPoint :
  ∀ {ℓ}
    (law : RepresentationKernelCompatibility {ℓ})
    {x : RepresentationKernelCompatibility.FineState law} →
  RepresentationKernelCompatibility.fineAdmissible law x →
  RepresentationKernelCompatibility.fineStep law x ≡ x →
  RepresentationKernelCompatibility.coarseStep law
    (RepresentationKernelCompatibility.project law x)
  ≡
  RepresentationKernelCompatibility.project law x
projectedFixedPoint law admissible fixed =
  trans
    (sym
      (RepresentationKernelCompatibility.kernelCommutesWithProjection
        law admissible))
    (cong
      (RepresentationKernelCompatibility.project law)
      fixed)

------------------------------------------------------------------------
-- Approximate/quotient compatibility.
--
-- This is the natural home for controlled coarse-graining, basis changes,
-- truncated carriers, residual defects, and universality-style claims.  The
-- relation is supplied explicitly; it is not inferred from numerical
-- closeness or low MDL cost alone.

record ApproxRepresentationKernelCompatibility {ℓ : Level} : Set (lsuc ℓ) where
  field
    FineState : Set ℓ
    CoarseState : Set ℓ
    Observable : Set ℓ

    fineStep : FineState → FineState
    coarseStep : CoarseState → CoarseState
    project : FineState → CoarseState

    fineAdmissible : FineState → Set ℓ
    coarseAdmissible : CoarseState → Set ℓ

    sameCoarsePhysics : CoarseState → CoarseState → Set ℓ
    sameObservable : Observable → Observable → Set ℓ

    fineObserve : FineState → Observable
    coarseObserve : CoarseState → Observable

    projectPreservesAdmissibility :
      ∀ {x} → fineAdmissible x → coarseAdmissible (project x)

    observableTransport :
      ∀ x → sameObservable (coarseObserve (project x)) (fineObserve x)

    kernelCommutesUpToPhysics :
      ∀ {x} →
      fineAdmissible x →
      sameCoarsePhysics
        (project (fineStep x))
        (coarseStep (project x))

------------------------------------------------------------------------
-- MDL is selection inside an already-lawful equivalence class.

record MDLRepresentativeSelection {ℓ : Level}
  (law : ApproxRepresentationKernelCompatibility {ℓ}) : Set (lsuc ℓ) where
  open ApproxRepresentationKernelCompatibility law
  field
    cost : CoarseState → Nat
    canonicalRepresentative : CoarseState → CoarseState

    representativePreservesPhysics :
      ∀ x → sameCoarsePhysics (canonicalRepresentative x) x

    representativeDoesNotIncreaseCost :
      ∀ x → cost (canonicalRepresentative x) ≤ cost x

    canonicalRepresentativeIdempotent :
      ∀ x →
      canonicalRepresentative (canonicalRepresentative x)
      ≡
      canonicalRepresentative x

------------------------------------------------------------------------
-- Foundations-facing receipt and strict boundaries.

record RepresentationKernelFoundationsReceipt : Setω where
  field
    plainQuestion : String
    relationToOperationOrder : String
    existingRepoAnchor : String
    establishedStructure : List String
    nonClaims : List String

canonicalRepresentationKernelFoundationsReceipt :
  RepresentationKernelFoundationsReceipt
canonicalRepresentationKernelFoundationsReceipt =
  record
    { plainQuestion =
        "How far may the state representation change while the same admissible dynamics, observables, and dynamical shapes remain?"
    ; relationToOperationOrder =
        "Wolfram varies the ordering of local operations; this surface varies the representation through which one and the same kernel law is read."
    ; existingRepoAnchor =
        "DASHI.Physics.Refinement already requires project(stepFine x) = stepCoarse(project x), exactly the strict commuting-square seed used here."
    ; establishedStructure =
        "exact projection/kernel commuting law"
        ∷ "admissibility transport between representations"
        ∷ "observable transport between representations"
        ∷ "fine fixed points project to coarse fixed points"
        ∷ "approximate law preservation through an explicit same-physics relation"
        ∷ "MDL selection occurs only inside an already supplied physical equivalence class"
        ∷ []
    ; nonClaims =
        "not a proof that all coarse-grainings preserve physics"
        ∷ "not a proof that every attractor or basin survives projection"
        ∷ "not a Wolfram causal-invariance theorem"
        ∷ "not a derivation of spacetime, quantum mechanics, or retrocausality"
        ∷ "not permission to identify low description length with physical truth"
        ∷ []
    }
