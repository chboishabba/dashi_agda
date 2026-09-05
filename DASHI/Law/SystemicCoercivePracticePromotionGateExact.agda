module DASHI.Law.SystemicCoercivePracticePromotionGateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.CoerciveEncounterPopulationAggregationExact as Population

------------------------------------------------------------------------
-- Population patterns do not automatically promote to systemic-practice or
-- pretext claims.  Promotion requires separate sampling/comparability and
-- interpretation receipts.
------------------------------------------------------------------------

data PopulationClaim : Set where
  descriptiveGatewayPattern systemicPractice pretextualIntent causalDeterrence : PopulationClaim

data PopulationProducer : Set where
  typedEncounterPopulation samplingFrame comparableEncounterDefinition
  transitionCrossTab repeatedPattern operationalPolicyReceipt intentReceipt
  counterfactualControl : PopulationProducer

record SystemicPromotionCutset : Set where
  constructor systemicPromotionCutset
  field
    population : Population.EncounterPopulation
    samplingFrameClosed : Bool
    comparabilityClosed : Bool
    transitionCrossTabClosed : Bool
    repeatedPatternClosed : Bool
    operationalPolicyClosed : Bool
    intentClosed : Bool
    counterfactualClosed : Bool
    cutsetReference : String

open SystemicPromotionCutset public

data PromotionResidual : Set where
  samplingFrameResidual comparabilityResidual transitionResidual repeatedPatternResidual
  operationalPolicyResidual intentResidual counterfactualResidual promotionClosed : PromotionResidual

firstSystemicResidual : PopulationClaim → SystemicPromotionCutset → PromotionResidual
firstSystemicResidual descriptiveGatewayPattern c with samplingFrameClosed c
... | false = samplingFrameResidual
... | true with comparabilityClosed c
...   | false = comparabilityResidual
...   | true with transitionCrossTabClosed c
...     | false = transitionResidual
...     | true = promotionClosed
firstSystemicResidual systemicPractice c with samplingFrameClosed c
... | false = samplingFrameResidual
... | true with comparabilityClosed c
...   | false = comparabilityResidual
...   | true with transitionCrossTabClosed c
...     | false = transitionResidual
...     | true with repeatedPatternClosed c
...       | false = repeatedPatternResidual
...       | true with operationalPolicyClosed c
...         | false = operationalPolicyResidual
...         | true = promotionClosed
firstSystemicResidual pretextualIntent c with samplingFrameClosed c
... | false = samplingFrameResidual
... | true with comparabilityClosed c
...   | false = comparabilityResidual
...   | true with transitionCrossTabClosed c
...     | false = transitionResidual
...     | true with repeatedPatternClosed c
...       | false = repeatedPatternResidual
...       | true with operationalPolicyClosed c
...         | false = operationalPolicyResidual
...         | true with intentClosed c
...           | false = intentResidual
...           | true = promotionClosed
firstSystemicResidual causalDeterrence c with counterfactualClosed c
... | false = counterfactualResidual
... | true = promotionClosed

------------------------------------------------------------------------
-- Concrete regression: even perfect descriptive transition counts do not
-- establish pretextual intent without an intent producer.
------------------------------------------------------------------------

canonicalDescriptiveOnlyCutset : SystemicPromotionCutset
canonicalDescriptiveOnlyCutset = systemicPromotionCutset
  Population.canonicalPopulation
  true true true true true false false
  "synthetic population has descriptive closure only; no intent/counterfactual receipt"

canonicalPretextStopsAtIntent :
  firstSystemicResidual pretextualIntent canonicalDescriptiveOnlyCutset ≡ intentResidual
canonicalPretextStopsAtIntent = refl

canonicalSystemicPracticeClosesWithoutIntent :
  firstSystemicResidual systemicPractice canonicalDescriptiveOnlyCutset ≡ promotionClosed
canonicalSystemicPracticeClosesWithoutIntent = refl

canonicalDeterrenceStillNeedsCounterfactual :
  firstSystemicResidual causalDeterrence canonicalDescriptiveOnlyCutset ≡ counterfactualResidual
canonicalDeterrenceStillNeedsCounterfactual = refl

------------------------------------------------------------------------
-- Claim-specific BIDI routing.
------------------------------------------------------------------------

reversePopulationClaim : PopulationClaim → PopulationProducer
reversePopulationClaim descriptiveGatewayPattern = transitionCrossTab
reversePopulationClaim systemicPractice = repeatedPattern
reversePopulationClaim pretextualIntent = intentReceipt
reversePopulationClaim causalDeterrence = counterfactualControl

record SystemicPromotionBoundary : Set where
  constructor systemicPromotionBoundary
  field
    oneEncounterProvesSystemicPractice : Bool
    oneEncounterProvesSystemicPracticeIsFalse : oneEncounterProvesSystemicPractice ≡ false
    highGatewayRateProvesPretextualIntent : Bool
    highGatewayRateProvesPretextualIntentIsFalse : highGatewayRateProvesPretextualIntent ≡ false
    repeatedPatternProvesIntent : Bool
    repeatedPatternProvesIntentIsFalse : repeatedPatternProvesIntent ≡ false
    descriptiveAssociationProvesDeterrence : Bool
    descriptiveAssociationProvesDeterrenceIsFalse : descriptiveAssociationProvesDeterrence ≡ false

canonicalSystemicPromotionBoundary : SystemicPromotionBoundary
canonicalSystemicPromotionBoundary =
  systemicPromotionBoundary false refl false refl false refl false refl
