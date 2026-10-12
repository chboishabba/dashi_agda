module DASHI.Economics.AIPolicyCausalAdmission20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIAustraliaRegulatoryPolicyAcquisition20261012Exact as Australia
import DASHI.Economics.AIRegulatoryBurdenConcentrationSensibLaw2026Exact as Burden

------------------------------------------------------------------------
-- POLICY FACT -> BURDEN MEASUREMENT -> REVIEWED CAUSAL ADMISSION
--
-- Cross-pollination from the SensibLaw/Friendlyjordies world-evidence lane:
-- observed institutional facts are not themselves a causal transition premise.
-- For AI policy, proposal/outcome facts, realised same-basis burden measurement,
-- and causal attribution to entry/concentration are separate proof obligations.
------------------------------------------------------------------------

australiaObservedPolicySubstratePaid : Bool
australiaObservedPolicySubstratePaid = true

sameBasisBurdenMeasurementStillOpen : Bool
sameBasisBurdenMeasurementStillOpen = true

reviewedCausalBridgeStillOpen : Bool
reviewedCausalBridgeStillOpen = true

intentionalCaptureStillSeparate : Bool
intentionalCaptureStillSeparate = true

record ObservedPolicySubstrate : Set where
  constructor observed-policy-substrate
  field
    proposalTextAcquired : Bool
    currentPolicyOutcomeAcquired : Bool
    regulatoryImpactSurveyAcquired : Bool
    realisedSameBasisCostsAcquired : Bool
    concentrationResponseObserved : Bool
    intentionalCaptureEvidenceAcquired : Bool

open ObservedPolicySubstrate public

australiaCurrentObservedPolicySubstrate : ObservedPolicySubstrate
australiaCurrentObservedPolicySubstrate = observed-policy-substrate
  true true true false false false

record ReviewedPolicyCausalBridge : Set₁ where
  constructor reviewed-policy-causal-bridge
  field
    evidenceRef : String
    reviewRef : String
    CausalPremise : Set
    causalPremiseWitness : CausalPremise
    sameBasisCostMeasurementPaid : Bool
    sameBasisCostMeasurementPaidIsTrue : sameBasisCostMeasurementPaid ≡ true
    marketResponseMeasurementPaid : Bool
    marketResponseMeasurementPaidIsTrue : marketResponseMeasurementPaid ≡ true
    establishesIntentionalCapture : Bool

open ReviewedPolicyCausalBridge public

-- No canonical ReviewedPolicyCausalBridge is supplied.  The current Australian
-- policy sources pay the proposal/outcome/survey substrate only.

currentSurveyStillLacksSameBasisCosts :
  Australia.harmonisedCostVectorAcquired Australia.regulatoryImpactSurveyAcquired ≡ false
currentSurveyStillLacksSameBasisCosts = Australia.sameBasisCostVectorStillOpen

currentBurdenOwnerStillLacksConcentrationResponse :
  Burden.concentrationEffectObserved Burden.currentRegulatoryBurdenResidual ≡ false
currentBurdenOwnerStillLacksConcentrationResponse = refl

currentCaptureOwnerStillDoesNotEstablishIntent :
  Burden.intentionalCaptureEstablished Burden.canonicalSafetyAndStructuralMoat ≡ false
currentCaptureOwnerStillDoesNotEstablishIntent = refl

data ObservedPolicyFactsCreateConcentrationCause : Set where
data StructuralAdvantageCreatesIntentionalCapture : Set where
data SurveyInstrumentCreatesRealisedCosts : Set where

observedPolicyFactsDoNotCreateConcentrationCause :
  ObservedPolicyFactsCreateConcentrationCause → ⊥
observedPolicyFactsDoNotCreateConcentrationCause ()

structuralAdvantageDoesNotCreateIntentionalCapture :
  StructuralAdvantageCreatesIntentionalCapture → ⊥
structuralAdvantageDoesNotCreateIntentionalCapture ()

surveyInstrumentDoesNotCreateRealisedCosts :
  SurveyInstrumentCreatesRealisedCosts → ⊥
surveyInstrumentDoesNotCreateRealisedCosts ()

policyCausalBoundary : String
policyCausalBoundary =
  "Observed Australian policy facts and a regulatory-impact survey are paid. Realised same-basis compliance costs, observed market response and a reviewed causal bridge from policy burden to entry/concentration remain separate. Structural incumbent advantage does not establish intentional capture."
