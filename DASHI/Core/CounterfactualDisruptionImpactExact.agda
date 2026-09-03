module DASHI.Core.CounterfactualDisruptionImpactExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- COUNTERFACTUAL DISRUPTION IMPACT / MATCHED-DEPARTURE CONTROL
--
-- Before asking who benefited from a person's loss, test whether the loss had
-- unusual capability consequences at all.  The comparison is against matched
-- ordinary departures/replacements, not against an imaginary world with zero
-- personnel turnover.
------------------------------------------------------------------------

data ImpactAxis : Set where
  milestoneDelay
  replacementLatency
  uniqueQualificationLoss
  knowledgeTransferGap
  programmeReorganisation
  fundingOrContractShift
  technicalPerformanceLoss
  noMeasuredImpact
  : ImpactAxis

data ImpactStatus : Set where
  impactPresent
  impactNotLocated
  impactKnownAbsent
  : ImpactStatus

record DepartureImpactProfile : Set where
  constructor departure-impact-profile
  field
    personOrRole : String
    capabilityOrProgramme : String
    impactAxes : List ImpactAxis
    status : ImpactStatus
    sourceReference : String
    boundedReading : String

open DepartureImpactProfile public

record MatchedDepartureControl : Set where
  constructor matched-departure-control
  field
    caseDeparture : DepartureImpactProfile
    matchingAxes : List String
    controlPopulation : String
    comparisonMeasure : String
    temporalWindow : String
    antiSelectionBiasRule : String

open MatchedDepartureControl public

record DisproportionateDisruption (design : MatchedDepartureControl) : Set where
  constructor disproportionate-disruption
  field
    measuredCaseImpact : String
    measuredControlImpact : String
    comparisonReceipt : String
    sameMeasureUsed : String

open DisproportionateDisruption public

record OrdinaryOrNullDisruption (design : MatchedDepartureControl) : Set where
  constructor ordinary-or-null-disruption
  field
    nullOrOrdinaryReceipt : String
    comparisonReference : String

open OrdinaryOrNullDisruption public

record CounterfactualImpactBoundary : Set where
  constructor counterfactual-impact-boundary
  field
    seniorTitleAutomaticallyMeansLowReplaceability : Bool
    seniorTitleAutomaticallyMeansLowReplaceabilityIsFalse :
      seniorTitleAutomaticallyMeansLowReplaceability ≡ false
    longTenureAutomaticallyMeansProgrammeDependsOnPerson : Bool
    longTenureAutomaticallyMeansProgrammeDependsOnPersonIsFalse :
      longTenureAutomaticallyMeansProgrammeDependsOnPerson ≡ false
    postLossDelayAutomaticallyProvesIntentionalDisruption : Bool
    postLossDelayAutomaticallyProvesIntentionalDisruptionIsFalse :
      postLossDelayAutomaticallyProvesIntentionalDisruption ≡ false
    matchedDepartureComparisonCanTestKeyPersonHypothesis : Bool
    matchedDepartureComparisonCanTestKeyPersonHypothesisIsTrue :
      matchedDepartureComparisonCanTestKeyPersonHypothesis ≡ true
    ordinaryImpactWeakensStrongDisruptionBenefitStory : Bool
    ordinaryImpactWeakensStrongDisruptionBenefitStoryIsTrue :
      ordinaryImpactWeakensStrongDisruptionBenefitStory ≡ true

canonicalCounterfactualImpactBoundary : CounterfactualImpactBoundary
canonicalCounterfactualImpactBoundary = counterfactual-impact-boundary
  false refl
  false refl
  false refl
  true refl
  true refl
