module DASHI.Cognition.ClinicToStreetsPromotionChainValidation where

open import DASHI.Core.Prelude

import DASHI.Cognition.ClinicToStreetsPromotionChainExact as Chain

stageCountRegression : Chain.stageCount ≡ 8
stageCountRegression = refl

sourceNotTruthRegression :
  Chain.sourceAttributionCreatesTruth Chain.canonicalPromotionChainBoundary ≡ false
sourceNotTruthRegression = refl

reviewNotIdentificationRegression :
  Chain.humanReviewCreatesCausalIdentification Chain.canonicalPromotionChainBoundary ≡ false
reviewNotIdentificationRegression = refl

identificationNotOutcomeRegression :
  Chain.identificationCreatesPatientOutcomeBenefit Chain.canonicalPromotionChainBoundary ≡ false
identificationNotOutcomeRegression = refl

implementationNotIntentRegression :
  Chain.implementationEffectCreatesInstitutionalIntent Chain.canonicalPromotionChainBoundary ≡ false
implementationNotIntentRegression = refl
