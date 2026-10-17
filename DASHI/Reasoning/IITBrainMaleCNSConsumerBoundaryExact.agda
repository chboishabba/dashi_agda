module DASHI.Reasoning.IITBrainMaleCNSConsumerBoundaryExact where

open import DASHI.Core.Prelude

import DASHI.Reasoning.BrainCognitionObservationSpineExact as Brain
import DASHI.Reasoning.MaleCNSConsumerRelativeLatentParetoExact as MaleCNS
import DASHI.Biology.ConsciousAccessCoalition as Access
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

------------------------------------------------------------------------
-- IIT / BRAIN / MALECNS CONSUMER BOUNDARY
--
-- This owner introduces no new neuroscience ontology.  It registers the IIT
-- integration score as one more candidate observation surface that must pay the
-- same consumer-relative adequacy obligations already enforced for connectome,
-- fMRI, behaviour, MaleCNS latents and conscious-access coalitions.
------------------------------------------------------------------------

BrainLatentQuery : Set
BrainLatentQuery = Brain.LatentConsumerQuery

BrainCandidateQuestion : Set
BrainCandidateQuestion = Brain.CandidateLatentConsumerQuestion

record IntegrationConsumerQuestion : Set where
  constructor integrationConsumerQuestion
  field
    integrationSurface : String
    declaredConsumer : BrainLatentQuery
    biologicalObservationSurface : String
    requiredFactorisationReceipt : String
    interpretationBoundary : String

open IntegrationConsumerQuestion public

memoryIntegrationQuestion : IntegrationConsumerQuestion
memoryIntegrationQuestion =
  integrationConsumerQuestion
    "declared IIT/system-integration observable"
    Brain.rememberedEventQuery
    "behavioural / connectome / fMRI / declared biological observation"
    "FactorsThrough observation remembered-event consumer, or explicit non-descent witness"
    "equal or high integration does not identify remembered semantic event identity"

policyIntegrationQuestion : IntegrationConsumerQuestion
policyIntegrationQuestion =
  integrationConsumerQuestion
    "declared IIT/system-integration observable"
    Brain.motorPolicyQuery
    "executed action / policy-labelled intervention surface"
    "consumer-relative factorisation plus intervention or same-object latent/behaviour binding"
    "action and integration scores do not manufacture policy identity"

data IntegrationScoreCreatesBiologicalIdentity : Set where

data PredictiveMetricCreatesConsumerAdequacy : Set where

data AccessCoalitionCreatesIITIdentity : Set where

integrationScoreDoesNotCreateBiologicalIdentity :
  IntegrationScoreCreatesBiologicalIdentity → ⊥
integrationScoreDoesNotCreateBiologicalIdentity ()

predictiveMetricDoesNotCreateConsumerAdequacy :
  PredictiveMetricCreatesConsumerAdequacy → ⊥
predictiveMetricDoesNotCreateConsumerAdequacy ()

accessCoalitionDoesNotCreateIITIdentity :
  AccessCoalitionCreatesIITIdentity → ⊥
accessCoalitionDoesNotCreateIITIdentity ()

record BrainMaleCNSIITBoundary : Set where
  constructor brainMaleCNSIITBoundary
  field
    latentFineStateToLossyObservationSpineAlreadyOwned : Bool
    consumerAdequacyPrecedesMetricRanking : Bool
    consciousAccessIsRelationalToContext : Bool
    IITScoreAutomaticallyDecodesMemoryIdentity : Bool
    IITScoreAutomaticallyDecodesMotorPolicy : Bool
    MaleCNSFitMetricAutomaticallyValidatesIIT : Bool
    consciousAccessCoalitionEqualsIITComplexByDefinition : Bool
    biologicalInterpretationRequiresSeparateSameObjectReceipts : Bool

open BrainMaleCNSIITBoundary public

canonicalBrainMaleCNSIITBoundary : BrainMaleCNSIITBoundary
canonicalBrainMaleCNSIITBoundary =
  brainMaleCNSIITBoundary
    true true true
    false false false false true

memoryIdentityNotReadOffIntegration :
  IITScoreAutomaticallyDecodesMemoryIdentity canonicalBrainMaleCNSIITBoundary ≡ false
memoryIdentityNotReadOffIntegration = refl

accessAndIITRemainSeparateTheories :
  consciousAccessCoalitionEqualsIITComplexByDefinition canonicalBrainMaleCNSIITBoundary ≡ false
accessAndIITRemainSeparateTheories = refl
