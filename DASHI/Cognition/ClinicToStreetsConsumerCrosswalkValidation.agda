module DASHI.Cognition.ClinicToStreetsConsumerCrosswalkValidation where

open import DASHI.Core.Prelude

import DASHI.Cognition.ClinicToStreetsConsumerCrosswalkExact as Crosswalk

consumerCountRegression : Crosswalk.consumerCount ≡ 12
consumerCountRegression = refl

approachCountRegression : Crosswalk.approachCount ≡ 5
approachCountRegression = refl

representationNotImplementationRegression :
  Crosswalk.representationalAdequacyImpliesImplementationFidelity
    Crosswalk.canonicalConsumerCrosswalkBoundary ≡ false
representationNotImplementationRegression = refl

implementationNotOutcomeRegression :
  Crosswalk.implementationFidelityImpliesPatientOutcomeBenefit
    Crosswalk.canonicalConsumerCrosswalkBoundary ≡ false
implementationNotOutcomeRegression = refl

patientVoiceNotProxyRegression :
  Crosswalk.proxyRepresentationReplacesPatientAuthoredRelevance
    Crosswalk.canonicalConsumerCrosswalkBoundary ≡ false
patientVoiceNotProxyRegression = refl

frameworkNotEfficacyRegression :
  Crosswalk.frameworkAlignmentCreatesComparativeEfficacy
    Crosswalk.canonicalConsumerCrosswalkBoundary ≡ false
frameworkNotEfficacyRegression = refl
