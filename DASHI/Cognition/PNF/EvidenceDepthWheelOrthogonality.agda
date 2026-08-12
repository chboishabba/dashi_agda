module DASHI.Cognition.PNF.EvidenceDepthWheelOrthogonality where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.RelationalHorizon369 as Horizon
import DASHI.Cognition.PNF.EvidenceHorizon369 as Evidence
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel
import DASHI.Reasoning.AttractorAlignedBranchSelection as Selection

------------------------------------------------------------------------
-- Relational horizon and refinement-wheel phase are independent coordinates.
------------------------------------------------------------------------

nextRelationalHorizon : Horizon.HorizonLevel → Horizon.HorizonLevel
nextRelationalHorizon Horizon.H3 = Horizon.H6
nextRelationalHorizon Horizon.H6 = Horizon.H9
nextRelationalHorizon Horizon.H9 = Horizon.H9

record HorizonDepthCoordinate : Set where
  constructor horizonDepthCoordinate
  field
    relationalHorizon : Horizon.HorizonLevel
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
-- Evidence sign/phase is a third, differently typed coordinate.
------------------------------------------------------------------------

record EvidenceDepthPhaseCoordinate : Set where
  constructor evidenceDepthPhaseCoordinate
  field
    evidenceDirection : Selection.InteractionDirection
    depthPhase : Wheel.DepthWheelPhase
    horizon : Horizon.HorizonLevel

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
    canonicalHorizonCoreReused : Bool
    canonicalHorizonCoreReusedIsTrue : canonicalHorizonCoreReused ≡ true

open EvidenceDepthWheelBoundary public

canonicalEvidenceDepthWheelBoundary : EvidenceDepthWheelBoundary
canonicalEvidenceDepthWheelBoundary =
  evidenceDepthWheelBoundary
    false refl
    false refl
    false refl
    true refl
    true refl

ExistingH3 : Set → Set
ExistingH3 = Evidence.H3Evidence
