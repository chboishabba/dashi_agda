module DASHI.Core.BoundaryObservationReconstructionExact where

------------------------------------------------------------------------
-- BOUNDARY OBSERVATION IS NOT RECONSTRUCTION WITHOUT A RECONSTRUCTION MAP
--
-- This is the observer/reopening statement behind the safe structural use of
-- "holographic" language in DASHI.  It does not import a physical AdS/CFT
-- theorem.  A boundary value is merely an observer value until an explicit
-- reconstruction law is supplied.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.ProvenanceBearingQuotient as Quotient
import DASHI.Core.ProvenanceFibreDynamicsReceiptExact as Provenance

record ExactBoundaryReconstruction
    {State Boundary : Set}
    (observe : Observer.Observer State Boundary) : Set₁ where
  constructor exactBoundaryReconstruction
  field
    reconstruct : Boundary → State
    reconstructExact : (state : State) → reconstruct (observe state) ≡ state

open ExactBoundaryReconstruction public

exactBoundaryReconstructionIsSeparating :
  ∀ {State Boundary : Set}
    {observe : Observer.Observer State Boundary} →
  ExactBoundaryReconstruction observe →
  Observer.Separating observe
exactBoundaryReconstructionIsSeparating reconstruction x y same =
  trans
    (sym (reconstructExact reconstruction x))
    (trans
      (cong (reconstruct reconstruction) same)
      (reconstructExact reconstruction y))

collisionBlocksExactBoundaryReconstruction :
  ∀ {State Boundary : Set}
    {observe : Observer.Observer State Boundary} →
  Observer.ObserverCollision observe →
  ExactBoundaryReconstruction observe →
  ⊥
collisionBlocksExactBoundaryReconstruction collision reconstruction =
  Observer.collisionBlocksSeparation collision
    (exactBoundaryReconstructionIsSeparating reconstruction)

------------------------------------------------------------------------
-- Relevant reconstruction is deliberately weaker than exact state recovery.
-- It is indexed by an application-supplied relevant equivalence/relation.
------------------------------------------------------------------------

record RelevantBoundaryReconstruction
    {State Boundary : Set}
    (Relevant : State → State → Set₁)
    (observe : Observer.Observer State Boundary) : Set₂ where
  constructor relevantBoundaryReconstruction
  field
    reconstructRelevant : Boundary → State
    reconstructRelevantSound :
      (state : State) → Relevant (reconstructRelevant (observe state)) state

open RelevantBoundaryReconstruction public

------------------------------------------------------------------------
-- Existing exact provenance-bearing quotients already provide a genuine
-- reconstructive encoding once the proof-relevant receipt is retained.
------------------------------------------------------------------------

provenanceSurfaceReceiptReconstruction :
  ∀ {core : Fibre.FibreRestrictionCore}
    (quotient : Quotient.ProvenanceBearingQuotient core) →
  ExactBoundaryReconstruction
    (Provenance.surfaceReceiptObserver quotient)
provenanceSurfaceReceiptReconstruction quotient =
  exactBoundaryReconstruction
    (λ pair → Quotient.reopen quotient (proj₁ pair) (proj₂ pair))
    (Quotient.reopenExact quotient)

record BoundaryObservationReconstructionBoundary : Set where
  constructor boundaryObservationReconstructionBoundary
  field
    boundaryObservationAloneImpliesExactReconstruction : Bool
    boundaryObservationAloneImpliesExactReconstructionIsFalse :
      boundaryObservationAloneImpliesExactReconstruction ≡ false
    exactReconstructionImpliesSeparation : Bool
    exactReconstructionImpliesSeparationIsTrue :
      exactReconstructionImpliesSeparation ≡ true
    relevantReconstructionIsWeakerThanExactRecovery : Bool
    relevantReconstructionIsWeakerThanExactRecoveryIsTrue :
      relevantReconstructionIsWeakerThanExactRecovery ≡ true
    surfacePlusExactReceiptCanReconstructFineState : Bool
    surfacePlusExactReceiptCanReconstructFineStateIsTrue :
      surfacePlusExactReceiptCanReconstructFineState ≡ true

canonicalBoundaryObservationReconstructionBoundary :
  BoundaryObservationReconstructionBoundary
canonicalBoundaryObservationReconstructionBoundary =
  boundaryObservationReconstructionBoundary
    false refl
    true refl
    true refl
    true refl
