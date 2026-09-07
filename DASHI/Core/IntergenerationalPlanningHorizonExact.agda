module DASHI.Core.IntergenerationalPlanningHorizonExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.HistoryConditionedChoiceExact as History

------------------------------------------------------------------------
-- INTERGENERATIONAL PLANNING HORIZON
--
-- DASHI-original planning calculus.
--
-- The seven-generation horizon below is represented as an explicit selected
-- planning horizon.  This file does NOT claim that a single universal
-- "seven generations" doctrine belongs to all Indigenous peoples, does NOT
-- identify it with any specific community's law without a community-specific
-- source receipt, and does NOT equate an integer horizon with Country law or
-- intergenerational authority.
------------------------------------------------------------------------

data Generation : Set where
  generation1 generation2 generation3 generation4 generation5 generation6 generation7 : Generation

data HorizonKind : Set where
  oneSeason : HorizonKind
  multiSeason : HorizonKind
  sevenGenerationHorizon : HorizonKind
  openEndedIntergenerationalHorizon : HorizonKind


record IntergenerationalHorizon : Set₁ where
  constructor intergenerational-horizon
  field
    horizonKind : HorizonKind
    State Action GenerationOutcome FutureCone : Set
    presentState : State
    act : State → Action → State
    outcomeAt : Generation → State → GenerationOutcome
    futureCone : State → FutureCone
    horizonReference : String
    authorityReference : String

open IntergenerationalHorizon public

record SevenGenerationInspection (horizon : IntergenerationalHorizon) : Set₁ where
  constructor seven-generation-inspection
  field
    outcome1 : GenerationOutcome horizon
    outcome2 : GenerationOutcome horizon
    outcome3 : GenerationOutcome horizon
    outcome4 : GenerationOutcome horizon
    outcome5 : GenerationOutcome horizon
    outcome6 : GenerationOutcome horizon
    outcome7 : GenerationOutcome horizon
    generation1Matches : outcome1 ≡ outcomeAt horizon generation1 (presentState horizon)
    generation2Matches : outcome2 ≡ outcomeAt horizon generation2 (presentState horizon)
    generation3Matches : outcome3 ≡ outcomeAt horizon generation3 (presentState horizon)
    generation4Matches : outcome4 ≡ outcomeAt horizon generation4 (presentState horizon)
    generation5Matches : outcome5 ≡ outcomeAt horizon generation5 (presentState horizon)
    generation6Matches : outcome6 ≡ outcomeAt horizon generation6 (presentState horizon)
    generation7Matches : outcome7 ≡ outcomeAt horizon generation7 (presentState horizon)

open SevenGenerationInspection public

record IntergenerationalImpactVector : Set₁ where
  constructor intergenerational-impact-vector
  field
    EcologicalIntegrity SoilState WaterState BiodiversityState ClimateExposure
      EconomicResilience DistributionState CulturalContinuity
      CountryAuthority FutureOptionSet Reversibility : Set
    ecologicalIntegrity : EcologicalIntegrity
    soilState : SoilState
    waterState : WaterState
    biodiversityState : BiodiversityState
    climateExposure : ClimateExposure
    economicResilience : EconomicResilience
    distributionState : DistributionState
    culturalContinuity : CulturalContinuity
    countryAuthority : CountryAuthority
    futureOptionSet : FutureOptionSet
    reversibility : Reversibility

open IntergenerationalImpactVector public

historyConditionedBoundary : History.HistoryConditionedChoiceBoundary
historyConditionedBoundary = History.canonicalHistoryConditionedChoiceBoundary

data PositivePresentBenefitImpliesPositiveSevenGenerationOutcomePermission : Set where
data PositiveGeneration7OutcomeImpliesNoIntermediateHarmPermission : Set where
data SevenGenerationHorizonImpliesCommunityAuthorityPermission : Set where
data DiscountedAggregateImpliesIntergenerationalJusticePermission : Set where
data ReversibleAtGeneration1ImpliesReversibleAtGeneration7Permission : Set where
data SamePresentStateImpliesSameLongHorizonFutureConePermission : Set where

presentBenefitDoesNotAutoPromoteAcrossSevenGenerations : PositivePresentBenefitImpliesPositiveSevenGenerationOutcomePermission → ⊥
presentBenefitDoesNotAutoPromoteAcrossSevenGenerations ()
generation7BenefitDoesNotEraseIntermediateHarm : PositiveGeneration7OutcomeImpliesNoIntermediateHarmPermission → ⊥
generation7BenefitDoesNotEraseIntermediateHarm ()
sevenGenerationHorizonDoesNotCreateCommunityAuthority : SevenGenerationHorizonImpliesCommunityAuthorityPermission → ⊥
sevenGenerationHorizonDoesNotCreateCommunityAuthority ()
discountedAggregateDoesNotAutoPromoteToIntergenerationalJustice : DiscountedAggregateImpliesIntergenerationalJusticePermission → ⊥
discountedAggregateDoesNotAutoPromoteToIntergenerationalJustice ()
shortRunReversibilityDoesNotAutoPromoteToLongRunReversibility : ReversibleAtGeneration1ImpliesReversibleAtGeneration7Permission → ⊥
shortRunReversibilityDoesNotAutoPromoteToLongRunReversibility ()
samePresentDoesNotAutoPromoteToSameLongHorizonFutureCone : SamePresentStateImpliesSameLongHorizonFutureConePermission → ⊥
samePresentDoesNotAutoPromoteToSameLongHorizonFutureCone ()

record IntergenerationalPlanningBoundary : Set where
  constructor intergenerational-planning-boundary
  field
    sevenGenerationHorizonIsExplicitPlanningChoice : Bool
    sevenGenerationHorizonIsExplicitPlanningChoiceIsTrue : sevenGenerationHorizonIsExplicitPlanningChoice ≡ true
    horizonLengthCreatesAuthority : Bool
    horizonLengthCreatesAuthorityIsFalse : horizonLengthCreatesAuthority ≡ false
    presentBenefitSufficesForLongHorizonDecision : Bool
    presentBenefitSufficesForLongHorizonDecisionIsFalse : presentBenefitSufficesForLongHorizonDecision ≡ false
    intermediateGenerationsMayCarryIndependentConstraints : Bool
    intermediateGenerationsMayCarryIndependentConstraintsIsTrue : intermediateGenerationsMayCarryIndependentConstraints ≡ true

canonicalIntergenerationalPlanningBoundary : IntergenerationalPlanningBoundary
canonicalIntergenerationalPlanningBoundary =
  intergenerational-planning-boundary true refl false refl false refl true refl
