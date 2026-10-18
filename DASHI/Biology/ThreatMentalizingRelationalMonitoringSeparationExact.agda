module DASHI.Biology.ThreatMentalizingRelationalMonitoringSeparationExact where

------------------------------------------------------------------------
-- THREAT / MENTALIZING / RELATIONAL MONITORING SEPARATION
--
-- DASHI CONTRIBUTION
--
-- M, T and R are independent finite coordinates:
--   M = general mentalizing quality
--   T = threat cue sensitivity/salience
--   R = relational monitoring/integration practice
--
-- Existing John Brown/religious-threat owners are imported as domain donors.
-- Their threat-comprehension, experienced-fear, behaviour-effect and truth
-- obligations remain independent.  No trauma history determines this state.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Culture.JohnAnthonyBrownChildReligiousPowerBidiExact as Brown
import DASHI.Culture.ReligiousThreatPredicateDialecticBidiExact as ReligiousThreat

data GeneralMentalizing : Set where
  lowerMentalizing : GeneralMentalizing
  preservedMentalizing : GeneralMentalizing
  higherMentalizing : GeneralMentalizing

data ThreatCueSensitivity : Set where
  ordinaryThreatCueSensitivity : ThreatCueSensitivity
  elevatedThreatCueSensitivity : ThreatCueSensitivity

data RelationalMonitoring : Set where
  ordinaryRelationalMonitoring : RelationalMonitoring
  elevatedRelationalMonitoring : RelationalMonitoring

data ResponsePolicy : Set where
  mediate : ResponsePolicy
  appease : ResponsePolicy
  avoid : ResponsePolicy
  intervene : ResponsePolicy
  freeze : ResponsePolicy
  dominate : ResponsePolicy

record MTRState : Set where
  constructor mtr-state
  field
    mentalizing : GeneralMentalizing
    threatSensitivity : ThreatCueSensitivity
    relationalMonitoring : RelationalMonitoring
    responsePolicy : ResponsePolicy

open MTRState public

highThreatHighMonitoringLowerMentalizing : MTRState
highThreatHighMonitoringLowerMentalizing =
  mtr-state
    lowerMentalizing
    elevatedThreatCueSensitivity
    elevatedRelationalMonitoring
    appease

highThreatHighMonitoringPreservedMentalizing : MTRState
highThreatHighMonitoringPreservedMentalizing =
  mtr-state
    preservedMentalizing
    elevatedThreatCueSensitivity
    elevatedRelationalMonitoring
    mediate

data ThreatSensitivityDeterminesMentalizing : Set where
data RelationalMonitoringDeterminesMentalizing : Set where
data ThreatSensitivityDeterminesResponsePolicy : Set where
data ThreatCueSensitivityEstablishesThreatTruth : Set where

threatSensitivityDoesNotDetermineMentalizing :
  ThreatSensitivityDeterminesMentalizing → ⊥
threatSensitivityDoesNotDetermineMentalizing ()

relationalMonitoringDoesNotDetermineMentalizing :
  RelationalMonitoringDeterminesMentalizing → ⊥
relationalMonitoringDoesNotDetermineMentalizing ()

threatSensitivityDoesNotDeterminePolicy :
  ThreatSensitivityDeterminesResponsePolicy → ⊥
threatSensitivityDoesNotDeterminePolicy ()

threatCueSensitivityDoesNotEstablishThreatTruth :
  ThreatCueSensitivityEstablishesThreatTruth → ⊥
threatCueSensitivityDoesNotEstablishThreatTruth ()

brownPaperKeepsUniqueFormationRouteBlocked =
  Brown.canonicalJohnAnthonyBrownPaperBidiBoundary

religiousThreatKeepsTruthAndEffectSeparate =
  ReligiousThreat.canonicalReligiousThreatPredicateDialecticBoundary

record MediationAffordanceBurdenState : Set where
  constructor mediation-affordance-burden-state
  field
    mediationSkill : Nat
    threatMonitoringCost : Nat
    selfAuthority : Nat
    otherModelResolution : Nat

highSkillHighCostLowSelf : MediationAffordanceBurdenState
highSkillHighCostLowSelf =
  mediation-affordance-burden-state 9 9 2 9

record ThreatMentalizingMonitoringBoundary : Set where
  constructor threat-mentalizing-monitoring-boundary
  field
    threatEqualsMentalizing : Bool
    monitoringEqualsMentalizing : Bool
    threatEqualsResponsePolicy : Bool
    threatCueEqualsThreatTruth : Bool
    highSkillCanCoexistWithHighCost : Bool
    highOtherResolutionCanCoexistWithLowSelfAuthority : Bool
    BrownThreatOwnersRetained : Bool

canonicalThreatMentalizingMonitoringBoundary :
  ThreatMentalizingMonitoringBoundary
canonicalThreatMentalizingMonitoringBoundary =
  threat-mentalizing-monitoring-boundary
    false false false false true true true
