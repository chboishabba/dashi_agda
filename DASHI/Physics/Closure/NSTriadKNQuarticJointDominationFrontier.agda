module DASHI.Physics.Closure.NSTriadKNQuarticJointDominationFrontier where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: David Darrow; Elizabeth Carlson; David Goluskin.
-- Title: "Quartic Lyapunov functions for global fluid stability".
-- Venue/year: arXiv preprint, 2026.
-- Journal DOI: none recorded on arXiv v1.
-- arXiv/DataCite DOI: 10.48550/arXiv.2606.18232.
-- arXiv: 2606.18232v1.
-- Uses: equations (21)--(22), joint domination of the sign-indefinite cubic
-- derivative by quadratic and quartic negative parts.
-- Relationship: contrasts the paper's 2-D shear-flow stability setting with
-- the DASHI-original arbitrary-data periodic 3-D cutoff-uniform target.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Nat.Base using (_≤_; _<_)

record CutoffUniformJointDomination {c s : Level} :
    Set (lsuc (c ⊔ s)) where
  field
    Cutoff : Set c
    State : Set s

    BoundaryState NonZeroState DangerousState :
      Cutoff → State → Set

    quadraticReserve cubicMagnitude quarticReserve :
      Cutoff → State → Nat

    cutoffUniformJointDomination : ∀ N state →
      BoundaryState N state →
      cubicMagnitude N state
      ≤ quadraticReserve N state + quarticReserve N state

    dominationStrictOnEveryNonzeroDangerousBoundaryState :
      ∀ N state →
      BoundaryState N state →
      NonZeroState N state →
      DangerousState N state →
      cubicMagnitude N state
      < quadraticReserve N state + quarticReserve N state

open CutoffUniformJointDomination public

jointDominationAvailableAtEveryBoundaryState :
  ∀ {c s}
    (D : CutoffUniformJointDomination {c} {s})
    (N : Cutoff D) (state : State D) →
  BoundaryState D N state →
  cubicMagnitude D N state
  ≤ quadraticReserve D N state + quarticReserve D N state
jointDominationAvailableAtEveryBoundaryState D N state =
  cutoffUniformJointDomination D N state

strictReserveAvailableAtEveryDangerousNonzeroBoundaryState :
  ∀ {c s}
    (D : CutoffUniformJointDomination {c} {s})
    (N : Cutoff D) (state : State D) →
  BoundaryState D N state →
  NonZeroState D N state →
  DangerousState D N state →
  cubicMagnitude D N state
  < quadraticReserve D N state + quarticReserve D N state
strictReserveAvailableAtEveryDangerousNonzeroBoundaryState D N state =
  dominationStrictOnEveryNonzeroDangerousBoundaryState D N state

jointDominationFrontierPreciselyTyped : Bool
jointDominationFrontierPreciselyTyped = true

jointDominationFrontierPreciselyTypedIsTrue :
  jointDominationFrontierPreciselyTyped ≡ true
jointDominationFrontierPreciselyTypedIsTrue = refl

cutoffUniformJointDominationClosed : Bool
cutoffUniformJointDominationClosed = false

cutoffUniformJointDominationClosedIsFalse :
  cutoffUniformJointDominationClosed ≡ false
cutoffUniformJointDominationClosedIsFalse = refl
