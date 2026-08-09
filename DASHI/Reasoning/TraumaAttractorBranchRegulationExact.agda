module DASHI.Reasoning.TraumaAttractorBranchRegulationExact where

open import DASHI.Core.Prelude

import DASHI.Reasoning.AttractorAlignedBranchSelectionExact as Branch
import DASHI.Reasoning.ChildhoodReligiousCoercionExact as Coercion

------------------------------------------------------------------------
-- Trauma-sensitive branch regulation.
--
-- Past unsafe closure can deform current branch policy in either direction:
-- branch hoarding or premature pruning.  The regulator must therefore use the
-- branch's current assessment rather than infer policy directly from trauma
-- history or observed compliance.
------------------------------------------------------------------------

data TraumaBranchDeformation : Set where
  noDeformation : TraumaBranchDeformation
  branchHoarding : TraumaBranchDeformation
  prematureClosure : TraumaBranchDeformation

data RawBranchPolicy : Set where
  keepEveryBranch : RawBranchPolicy
  closeEveryUncertainBranch : RawBranchPolicy
  assessCurrentMarginalValue : RawBranchPolicy

deformedPolicy : TraumaBranchDeformation → RawBranchPolicy
deformedPolicy noDeformation = assessCurrentMarginalValue
deformedPolicy branchHoarding = keepEveryBranch
deformedPolicy prematureClosure = closeEveryUncertainBranch

hoardingKeepsEverything :
  deformedPolicy branchHoarding ≡ keepEveryBranch
hoardingKeepsEverything = refl

prematureClosureClosesUncertainty :
  deformedPolicy prematureClosure ≡ closeEveryUncertainBranch
prematureClosureClosesUncertainty = refl

regulatedDecision :
  TraumaBranchDeformation →
  Branch.Branch →
  Branch.MarginalDecision
regulatedDecision deformation candidate = Branch.marginalDecision candidate

regulationOverridesHoardingForTrapBranch :
  regulatedDecision branchHoarding Branch.attractiveDeadEnd
  ≡ Branch.pruneBranch
regulationOverridesHoardingForTrapBranch = refl

regulationOverridesPrematureClosureForExploration :
  regulatedDecision prematureClosure Branch.exploratoryRoute
  ≡ Branch.retainBranch
regulationOverridesPrematureClosureForExploration = refl

data SafetySignal : Set where
  safeContext : SafetySignal
  coerciveContext : SafetySignal

safetyFromRelationalStructure :
  Coercion.CoercionStatus → SafetySignal
safetyFromRelationalStructure Coercion.nonCoercive = safeContext
safetyFromRelationalStructure Coercion.coercive = coerciveContext

coerciveDemandIsUnsafeContext :
  safetyFromRelationalStructure
    (Coercion.coercionFrom
      Coercion.complianceDemanded
      Coercion.penalisedRefusal
      Coercion.seriousPenalty)
  ≡ coerciveContext
coerciveDemandIsUnsafeContext = refl

data RegulationAuthority : Set where
  historyOnly : RegulationAuthority
  currentAssessment : RegulationAuthority

record TraumaSensitiveBranchRegulator : Set where
  constructor traumaSensitiveBranchRegulator
  field
    decide :
      TraumaBranchDeformation →
      Branch.Branch →
      Branch.MarginalDecision
    safety : Coercion.CoercionStatus → SafetySignal
    authority : RegulationAuthority
    traumaHistoryAloneDeterminesDecision : Bool
    traumaHistoryAloneDeterminesDecisionIsFalse :
      traumaHistoryAloneDeterminesDecision ≡ false

canonicalTraumaSensitiveBranchRegulator : TraumaSensitiveBranchRegulator
canonicalTraumaSensitiveBranchRegulator =
  traumaSensitiveBranchRegulator
    regulatedDecision
    safetyFromRelationalStructure
    currentAssessment
    false refl

------------------------------------------------------------------------
-- The central two-sided correction: neither keep-all nor close-all is sound.
------------------------------------------------------------------------

record TwoSidedRegulationWitness : Set where
  constructor twoSidedRegulationWitness
  field
    retainedDespitePrematureClosurePressure :
      regulatedDecision prematureClosure Branch.exploratoryRoute
      ≡ Branch.retainBranch
    prunedDespiteHoardingPressure :
      regulatedDecision branchHoarding Branch.attractiveDeadEnd
      ≡ Branch.pruneBranch

healthyRegulationIsContextSensitive : TwoSidedRegulationWitness
healthyRegulationIsContextSensitive =
  twoSidedRegulationWitness refl refl
