{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayNormalizedExpectationRepresentationFirewallRound448Validation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayNormalizedExpectationRepresentationFirewallRound448Exact as R448

normalizedDoesNotRecoverNumerator :
  R448.normalizedExpectationAgreementImpliesRawNumeratorAgreement ≡ false
normalizedDoesNotRecoverNumerator = refl

normalizedDoesNotRecoverPartitionFunction :
  R448.normalizedExpectationAgreementImpliesPartitionFunctionAgreement ≡ false
normalizedDoesNotRecoverPartitionFunction = refl

normalizedLimitIsNotMeasureConstruction :
  R448.normalizedExpectationLimitAloneImpliesCountablyAdditiveMeasure ≡ false
normalizedLimitIsNotMeasureConstruction = refl

expectationCarrierIsNotRepresentationByName :
  R448.expectationFunctionalCarrierAloneIsMeasureRepresentation ≡ false
expectationCarrierIsNotRepresentationByName = refl

representationRequiresCountableAdditivity :
  R448.continuumRepresentationRequiresCountableAdditivity ≡ true
representationRequiresCountableAdditivity = refl

representationRequiresExpectationIdentification :
  R448.continuumRepresentationRequiresExpectationIdentification ≡ true
representationRequiresExpectationIdentification = refl

representedExpectationNotIndependentlyChosen :
  R448.representedExpectationChosenIndependentlyFromMeasure ≡ false
representedExpectationNotIndependentlyChosen = refl

representedExpectationByIntegrationDefinitional :
  R448.representedExpectationByIntegrationIsDefinitional ≡ true
representedExpectationByIntegrationDefinitional = refl
