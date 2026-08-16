module DASHI.Crypto.ProtectedLabelSearchGeometryExact where

------------------------------------------------------------------------
-- PROTECTED-LABEL SEARCH GEOMETRY
--
-- Candidate fibres are not treated merely as finite sets.  A recovery
-- architecture also chooses admissible search transitions, a representation,
-- and a transition/update cost.  This is the crypto specialization of the
-- quotient + rate + geometry programme: candidate count and search geometry
-- are separate coordinates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

record ProtectedLabelSearchGeometry : Set₁ where
  constructor protectedLabelSearchGeometry
  field
    Hidden Public Protected Code : Set
    project : Hidden → Public
    protected : Hidden → Protected
    Candidate : Public → Hidden → Set
    SearchEdge : Public → Hidden → Hidden → Set
    encode : Hidden → Code
    edgeUpdateCost :
      ∀ {public left right} → SearchEdge public left right → Nat

open ProtectedLabelSearchGeometry public

record SearchStep
    (geometry : ProtectedLabelSearchGeometry)
    (public : Public geometry) : Set₁ where
  constructor searchStep
  field
    from to : Hidden geometry
    fromCandidate : Candidate geometry public from
    toCandidate : Candidate geometry public to
    edge : SearchEdge geometry public from to

open SearchStep public

stepCost :
  ∀ {geometry public} → SearchStep geometry public → Nat
stepCost {geometry} step = edgeUpdateCost geometry (edge step)

pathCost :
  ∀ {geometry public} → List (SearchStep geometry public) → Nat
pathCost [] = 0
pathCost (step ∷ steps) = stepCost step + pathCost steps

record SameInformationDifferentGeometry : Set₁ where
  constructor sameInformationDifferentGeometry
  field
    State CodeA CodeB : Set
    encodeA : State → CodeA
    encodeB : State → CodeB
    stateCount : Nat
    rateA rateB : Nat
    sameRate : rateA ≡ rateB
    transitionCostA transitionCostB : Nat

open SameInformationDifferentGeometry public

record GeometricObservationUpdate : Set where
  constructor geometricObservationUpdate
  field
    candidatesBefore candidatesAfter : Nat
    graphCostBefore graphCostAfter : Nat
    reconcileBefore reconcileAfter : Nat
    observationCost : Nat

open GeometricObservationUpdate public

recoveryCostBefore : GeometricObservationUpdate → Nat
recoveryCostBefore update = graphCostBefore update + reconcileBefore update

recoveryCostAfter : GeometricObservationUpdate → Nat
recoveryCostAfter update =
  observationCost update + graphCostAfter update + reconcileAfter update

record GeometryImprovement (update : GeometricObservationUpdate) : Set where
  constructor geometryImprovement
  field
    gain : Nat
    exactGain : recoveryCostBefore update ≡ recoveryCostAfter update + gain

open GeometryImprovement public

------------------------------------------------------------------------
-- Regression: equal candidate-count reduction can have opposite geometry.
------------------------------------------------------------------------

beneficialGeometryUpdate : GeometricObservationUpdate
beneficialGeometryUpdate = geometricObservationUpdate 8 7 20 8 8 2

beneficialGeometryGain : GeometryImprovement beneficialGeometryUpdate
beneficialGeometryGain = geometryImprovement 15 refl

sameCountBadGeometry : GeometricObservationUpdate
sameCountBadGeometry = geometricObservationUpdate 8 7 4 15 0 0

sameCandidateShrinkDifferentGeometry :
  candidatesBefore beneficialGeometryUpdate ≡ candidatesBefore sameCountBadGeometry
  × candidatesAfter beneficialGeometryUpdate ≡ candidatesAfter sameCountBadGeometry
sameCandidateShrinkDifferentGeometry = refl , refl

sameShrinkCanHaveOppositeRecoveryGeometry :
  recoveryCostBefore sameCountBadGeometry ≡ 4
  × recoveryCostAfter sameCountBadGeometry ≡ 15
sameShrinkCanHaveOppositeRecoveryGeometry = refl , refl
