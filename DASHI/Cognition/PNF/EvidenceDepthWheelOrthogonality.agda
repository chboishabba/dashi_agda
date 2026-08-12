module DASHI.Cognition.PNF.EvidenceDepthWheelOrthogonality where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.PNF.EvidenceHorizon369 as Evidence
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection

------------------------------------------------------------------------
-- Relational horizon and refinement-wheel phase are independent coordinates.
------------------------------------------------------------------------

data RelationalHorizon : Set where
  horizon3 horizon6 horizon9 : RelationalHorizon

nextRelationalHorizon : RelationalHorizon → RelationalHorizon
nextRelationalHorizon horizon3 = horizon6
nextRelationalHorizon horizon6 = horizon9
nextRelationalHorizon horizon9 = horizon9

record HorizonDepthCoordinate : Set where
  constructor horizonDepthCoordinate
  field
    relationalHorizon : RelationalHorizon
    refinementPhase : Wheel.DepthWheelPhase

open HorizonDepthCoordinate public

expandHorizon : HorizonDepthCoordinate → HorizonDepthCoordinate
expandHorizon coordinate =
  horizonDepthCoordinate
    (nextRelationalHorizon (relationalHorizon coordinate))
    (refinementPhase coordinate)

advanceDepthPhase : HorizonDepthCoordinate → HorizonDepthCoordinate
advanceDepthPhase coordinate =
  horizonDepthCoordinate
    (relationalHorizon coordinate)
    (Wheel.nextDepthWheelPhase (refinementPhase coordinate))

horizonExpansionCommutesWithDepthAdvance :
  (coordinate : HorizonDepthCoordinate) →
  advanceDepthPhase (expandHorizon coordinate)
  ≡ expandHorizon (advanceDepthPhase coordinate)
horizonExpansionCommutesWithDepthAdvance coordinate = refl

------------------------------------------------------------------------
-- Evidence sign/phase is a third, differently typed coordinate.  It is the
-- coarse classification of signed evidence, not the refinement-wheel grade.
------------------------------------------------------------------------

record EvidenceDepthPhaseCoordinate : Set where
  constructor evidenceDepthPhaseCoordinate
  field
    evidenceDirection : Selection.InteractionDirection
    depthPhase : Wheel.DepthWheelPhase
    horizon : RelationalHorizon

open EvidenceDepthPhaseCoordinate public

record EvidenceDepthWheelBoundary : Set where
  constructor evidenceDepthWheelBoundary
  field
    horizonIsCandidateCardinality : Bool
    horizonIsCandidateCardinalityIsFalse :
      horizonIsCandidateCardinality ≡ false
    evidencePhaseIsDepthPhase : Bool
    evidencePhaseIsDepthPhaseIsFalse : evidencePhaseIsDepthPhase ≡ false
    depthPhaseIsRelationalHorizon : Bool
    depthPhaseIsRelationalHorizonIsFalse :
      depthPhaseIsRelationalHorizon ≡ false
    horizonAndDepthActionsCommute : Bool
    horizonAndDepthActionsCommuteIsTrue :
      horizonAndDepthActionsCommute ≡ true
    existingH369CarrierReused : Bool
    existingH369CarrierReusedIsTrue : existingH369CarrierReused ≡ true

open EvidenceDepthWheelBoundary public

canonicalEvidenceDepthWheelBoundary : EvidenceDepthWheelBoundary
canonicalEvidenceDepthWheelBoundary =
  evidenceDepthWheelBoundary
    false refl
    false refl
    false refl
    true refl
    true refl

-- Type-level reference to the existing specialised H3/H6/H9 carrier.  This is
-- deliberately not redefined by the orthogonality module.
ExistingH3 : Set → Set
ExistingH3 = Evidence.H3Evidence
