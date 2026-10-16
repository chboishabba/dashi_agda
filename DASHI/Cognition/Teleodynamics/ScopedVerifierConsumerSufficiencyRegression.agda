module DASHI.Cognition.Teleodynamics.ScopedVerifierConsumerSufficiencyRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Cognition.Teleodynamics.ScopedVerifierConsumerSufficiencyExact as Consumer

consumerAdequacyIsRelative :
  Consumer.ConsumerSufficiencyBoundary.consumerRelativeAdequacyRequired
    Consumer.canonicalConsumerSufficiencyBoundary ≡ true
consumerAdequacyIsRelative = refl

canonicalQueryFactorisationIsReused :
  Consumer.ConsumerSufficiencyBoundary.canonicalQueryFactorsThroughReused
    Consumer.canonicalConsumerSufficiencyBoundary ≡ true
canonicalQueryFactorisationIsReused = refl

canonicalConsumerSufficiencyIsReused :
  Consumer.ConsumerSufficiencyBoundary.canonicalConsumerSufficientReused
    Consumer.canonicalConsumerSufficiencyBoundary ≡ true
canonicalConsumerSufficiencyIsReused = refl

admissibilityAndAdequacyStaySeparate :
  Consumer.ConsumerSufficiencyBoundary.admissibilitySeparatedFromConsumerAdequacy
    Consumer.canonicalConsumerSufficiencyBoundary ≡ true
admissibilityAndAdequacyStaySeparate = refl

eligibilityUsesExistingMDLSpine :
  Consumer.ConsumerSufficiencyBoundary.eligibilityIsAdmissibleAndConsumerAdequate
    Consumer.canonicalConsumerSufficiencyBoundary ≡ true
eligibilityUsesExistingMDLSpine = refl

localDuplicateFactorisationIsRetired :
  Consumer.ConsumerSufficiencyBoundary.localFactorisationCalculusRetired
    Consumer.canonicalConsumerSufficiencyBoundary ≡ true
localDuplicateFactorisationIsRetired = refl

coarseCollisionAloneIsNotFailure :
  Consumer.ConsumerSufficiencyBoundary.coarseCollisionAloneImpliesFailure
    Consumer.canonicalConsumerSufficiencyBoundary ≡ false
coarseCollisionAloneIsNotFailure = refl

validatorPassDoesNotPayEveryConsumer :
  Consumer.ConsumerSufficiencyBoundary.validatorPassImpliesAllConsumerSufficiency
    Consumer.canonicalConsumerSufficiencyBoundary ≡ false
validatorPassDoesNotPayEveryConsumer = refl

repairNeedsCanonicalSufficiency :
  Consumer.ConsumerSufficiencyBoundary.refinementRequiresCanonicalConsumerSufficiency
    Consumer.canonicalConsumerSufficiencyBoundary ≡ true
repairNeedsCanonicalSufficiency = refl

provenanceQueryReallyFactors :
  Query.FactorsThrough
    Consumer.verifierQuestions
    Consumer.provenanceAwareView
    Consumer.provenanceQuery
provenanceQueryReallyFactors = Consumer.provenanceQueryFactors

syntaxModelIsAdmissible :
  MDL.Admissible Consumer.verifierObservationProblem Consumer.syntaxOnlyModel
syntaxModelIsAdmissible = Consumer.syntaxModelAdmissible

syntaxModelStillNotEligible :
  MDL.Eligible Consumer.verifierObservationProblem Consumer.syntaxOnlyModel → ⊥
syntaxModelStillNotEligible = Consumer.syntaxModelNotEligible

provenanceModelIsEligible :
  MDL.Eligible Consumer.verifierObservationProblem Consumer.provenanceAwareModel
provenanceModelIsEligible = Consumer.provenanceModelEligible
