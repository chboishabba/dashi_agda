module DASHI.Promotion.TechSystemicStressScenarioRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.SSPTritCarrier as Trit
import DASHI.Promotion.TechSystemicStressScenarioBoundary as Stress

------------------------------------------------------------------------
-- Compact regression surface for the candidate-only stress machine.

negativeRegimeMeansAdverse :
  Stress.regimeMeaning Trit.sspNegOne
  ≡
  Stress.adverseStructuralRegime
negativeRegimeMeansAdverse = refl

zeroRegimeMeansUnresolved :
  Stress.regimeMeaning Trit.sspZero
  ≡
  Stress.unresolvedStructuralRegime
zeroRegimeMeansUnresolved = refl

positiveRegimeMeansFavorable :
  Stress.regimeMeaning Trit.sspPosOne
  ≡
  Stress.favorableStructuralRegime
positiveRegimeMeansFavorable = refl

negativeRegimeSelectsDefensivePosture :
  Stress.postureFromRegime Trit.sspNegOne
  ≡
  Stress.defensivePosture
negativeRegimeSelectsDefensivePosture = refl

zeroRegimeSelectsObservationalPosture :
  Stress.postureFromRegime Trit.sspZero
  ≡
  Stress.observationalPosture
zeroRegimeSelectsObservationalPosture = refl

positiveRegimeSelectsOpportunityPosture :
  Stress.postureFromRegime Trit.sspPosOne
  ≡
  Stress.opportunityPosture
positiveRegimeSelectsOpportunityPosture = refl

canonicalMachineSeparatesLayers :
  Stress.observationClassificationPostureExecutionSeparated
    Stress.canonicalTechSystemicStressMachine
  ≡
  true
canonicalMachineSeparatesLayers = refl

canonicalMachineDoesNotReadRegimeAsPriceDirection :
  Stress.signedRegimeIsNotPriceDirection
    Stress.canonicalTechSystemicStressMachine
  ≡
  true
canonicalMachineDoesNotReadRegimeAsPriceDirection = refl

canonicalMachineHasNoMarketPredictionAuthority :
  Stress.marketPredictionAuthority
    Stress.canonicalTechSystemicStressMachine
  ≡
  false
canonicalMachineHasNoMarketPredictionAuthority = refl

canonicalMachineHasNoFinancialAdviceAuthority :
  Stress.financialAdviceAuthority
    Stress.canonicalTechSystemicStressMachine
  ≡
  false
canonicalMachineHasNoFinancialAdviceAuthority = refl

canonicalMachineHasNoProductionExecutionAuthority :
  Stress.productionExecutionAuthority
    Stress.canonicalTechSystemicStressMachine
  ≡
  false
canonicalMachineHasNoProductionExecutionAuthority = refl

canonicalGreeceFixtureIsPostHocOnly :
  Stress.postHocAlignmentOnly
    Stress.canonicalGreeceStyleAttributionCandidate
  ≡
  true
canonicalGreeceFixtureIsPostHocOnly = refl

canonicalGreeceFixtureDoesNotPromoteCausality :
  Stress.causalAttributionPromoted
    Stress.canonicalGreeceStyleAttributionCandidate
  ≡
  false
canonicalGreeceFixtureDoesNotPromoteCausality = refl

canonicalAIFixtureDoesNotPredictHeadlines :
  Stress.headlinePredictionPromoted
    Stress.canonicalAIStressAttributionCandidate
  ≡
  false
canonicalAIFixtureDoesNotPredictHeadlines = refl
