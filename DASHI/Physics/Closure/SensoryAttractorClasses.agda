module DASHI.Physics.Closure.SensoryAttractorClasses where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Generic sensory transport and attractor vocabulary.
--
-- This is a receipt surface, not an empirical biology theorem.  It records
-- the typed spine from world physics to retained behavioral quotients while
-- keeping qualia recovery, arbitrary cross-sense identity, and unsupported
-- biological theorem claims explicitly blocked.

data SensoryTransportLayer : Set where
  worldPhysicsLayer : SensoryTransportLayer
  physicalTransportLayer : SensoryTransportLayer
  receptorChemistryLayer : SensoryTransportLayer
  neuralEncodingLayer : SensoryTransportLayer
  connectomeBodyPropagationLayer : SensoryTransportLayer
  perceptualBehaviorQuotientLayer : SensoryTransportLayer
  evolutionaryRetentionLayer : SensoryTransportLayer

defaultSensoryTransportPipeline : List SensoryTransportLayer
defaultSensoryTransportPipeline =
  worldPhysicsLayer
  ∷ physicalTransportLayer
  ∷ receptorChemistryLayer
  ∷ neuralEncodingLayer
  ∷ connectomeBodyPropagationLayer
  ∷ perceptualBehaviorQuotientLayer
  ∷ evolutionaryRetentionLayer
  ∷ []

data SensoryModalityClass : Set where
  visualLike : SensoryModalityClass
  auditoryLike : SensoryModalityClass
  chemosensoryLike : SensoryModalityClass
  magnetosensoryLike : SensoryModalityClass
  mechanosensoryLike : SensoryModalityClass
  thermosensoryLike : SensoryModalityClass
  interoceptiveLike : SensoryModalityClass
  multimodalLike : SensoryModalityClass

data LowDimensionalAttractorClass : Set where
  fixedPointClass : LowDimensionalAttractorClass
  limitCycleClass : LowDimensionalAttractorClass
  torusClass : LowDimensionalAttractorClass
  heteroclinicChannelClass : LowDimensionalAttractorClass
  metastableBasinClass : LowDimensionalAttractorClass
  quasiPotentialValleyClass : LowDimensionalAttractorClass
  policyManifoldClass : LowDimensionalAttractorClass

data EvolutionaryRetentionCriterion : Set where
  survivalProxyImproves : EvolutionaryRetentionCriterion
  reproductionProxyImproves : EvolutionaryRetentionCriterion
  energyCostReduced : EvolutionaryRetentionCriterion
  developmentalRobustnessImproves : EvolutionaryRetentionCriterion
  environmentalRobustnessImproves : EvolutionaryRetentionCriterion
  socialOrEcologicalPolicyImproves : EvolutionaryRetentionCriterion

data SensoryTransportNonPromotionBoundary : Set where
  noExactQualiaRecovery : SensoryTransportNonPromotionBoundary
  noArbitraryCrossSenseIdentity : SensoryTransportNonPromotionBoundary
  noTheoremLevelBiologyClaimWithoutReceipts :
    SensoryTransportNonPromotionBoundary
  noLatentStateInjection : SensoryTransportNonPromotionBoundary
  noEvolutionaryOptimalityClaim : SensoryTransportNonPromotionBoundary
  noEmpiricalValidationWithoutMeasurementReceipt :
    SensoryTransportNonPromotionBoundary

------------------------------------------------------------------------
-- World physics -> transport -> chemistry -> neural/body propagation ->
-- perceptual/behavior quotient -> evolutionary retention.

record GeneralizedSensoryTransport : Set₁ where
  field
    WorldPhysics : Set
    Environment : Set
    PhysicalTransport : Set
    ReceptorChemistry : Set
    NeuralEncoding : Set
    ConnectomeBodyState : Set
    PerceptualBehaviorClass : Set
    EvolutionaryLineage : Set
    FitnessSignal : Set

    modalityClass :
      WorldPhysics →
      SensoryModalityClass

    worldToPhysicalTransport :
      WorldPhysics →
      Environment →
      PhysicalTransport

    physicalTransportToReceptorChemistry :
      PhysicalTransport →
      ReceptorChemistry

    receptorChemistryToNeuralEncoding :
      ReceptorChemistry →
      NeuralEncoding

    neuralEncodingToConnectomeBodyPropagation :
      NeuralEncoding →
      ConnectomeBodyState →
      ConnectomeBodyState

    connectomeBodyToPerceptualBehaviorQuotient :
      ConnectomeBodyState →
      PerceptualBehaviorClass

    perceptualBehaviorToEvolutionaryRetention :
      PerceptualBehaviorClass →
      EvolutionaryLineage →
      FitnessSignal

    retainedUnder :
      FitnessSignal →
      EvolutionaryRetentionCriterion →
      Set

    samePerceptualBehaviorClass :
      PerceptualBehaviorClass →
      PerceptualBehaviorClass →
      Set

    crossSenseComparisonReceipt :
      SensoryModalityClass →
      SensoryModalityClass →
      Set

    pipeline :
      List SensoryTransportLayer

    transportReading :
      String

open GeneralizedSensoryTransport public

sensoryPipelineFromWorld :
  (transport : GeneralizedSensoryTransport) →
  WorldPhysics transport →
  Environment transport →
  ConnectomeBodyState transport →
  PerceptualBehaviorClass transport
sensoryPipelineFromWorld transport world environment body =
  connectomeBodyToPerceptualBehaviorQuotient transport
    (neuralEncodingToConnectomeBodyPropagation transport
      (receptorChemistryToNeuralEncoding transport
        (physicalTransportToReceptorChemistry transport
          (worldToPhysicalTransport transport world environment)))
      body)

sensoryRetentionSignalFromWorld :
  (transport : GeneralizedSensoryTransport) →
  WorldPhysics transport →
  Environment transport →
  ConnectomeBodyState transport →
  EvolutionaryLineage transport →
  FitnessSignal transport
sensoryRetentionSignalFromWorld transport world environment body lineage =
  perceptualBehaviorToEvolutionaryRetention transport
    (sensoryPipelineFromWorld transport world environment body)
    lineage

record LowDimensionalSensoryAttractor
    (transport : GeneralizedSensoryTransport) : Set₁ where
  field
    AttractorCoordinate : Set
    ResidualWidth : Set

    attractorClass :
      LowDimensionalAttractorClass

    coordinateFromNeuralEncoding :
      NeuralEncoding transport →
      AttractorCoordinate

    coordinateFromConnectomeBody :
      ConnectomeBodyState transport →
      AttractorCoordinate

    coordinateFromPerceptualBehavior :
      PerceptualBehaviorClass transport →
      AttractorCoordinate

    coordinateStep :
      AttractorCoordinate →
      AttractorCoordinate

    basin :
      AttractorCoordinate →
      Set

    residualWidth :
      AttractorCoordinate →
      ResidualWidth

    quotientRespectsAttractorClass :
      PerceptualBehaviorClass transport →
      Set

    lowDimensionalReading :
      String

open LowDimensionalSensoryAttractor public

record EvolvedLowDimensionalSensoryAttractor
    (transport : GeneralizedSensoryTransport) : Set₁ where
  field
    attractor :
      LowDimensionalSensoryAttractor transport

    retainedCoordinate :
      AttractorCoordinate attractor →
      EvolutionaryLineage transport →
      EvolutionaryRetentionCriterion →
      Set

    retainedBehaviorQuotient :
      PerceptualBehaviorClass transport →
      EvolutionaryLineage transport →
      EvolutionaryRetentionCriterion →
      Set

    behavioralRetentionFactors :
      List EvolutionaryRetentionCriterion

    retentionReading :
      String

open EvolvedLowDimensionalSensoryAttractor public

record SensoryTransportNonPromotionCertificate
    (transport : GeneralizedSensoryTransport) : Set where
  field
    boundaries :
      List SensoryTransportNonPromotionBoundary

    exactQualiaRecovery :
      Bool

    exactQualiaRecoveryIsFalse :
      exactQualiaRecovery ≡ false

    arbitraryCrossSenseIdentity :
      Bool

    arbitraryCrossSenseIdentityIsFalse :
      arbitraryCrossSenseIdentity ≡ false

    theoremLevelBiologyClaimWithoutReceipts :
      Bool

    theoremLevelBiologyClaimWithoutReceiptsIsFalse :
      theoremLevelBiologyClaimWithoutReceipts ≡ false

    latentStateInjection :
      Bool

    latentStateInjectionIsFalse :
      latentStateInjection ≡ false

    boundaryReading :
      String

open SensoryTransportNonPromotionCertificate public

canonicalSensoryTransportNonPromotionBoundaries :
  List SensoryTransportNonPromotionBoundary
canonicalSensoryTransportNonPromotionBoundaries =
  noExactQualiaRecovery
  ∷ noArbitraryCrossSenseIdentity
  ∷ noTheoremLevelBiologyClaimWithoutReceipts
  ∷ noLatentStateInjection
  ∷ noEvolutionaryOptimalityClaim
  ∷ noEmpiricalValidationWithoutMeasurementReceipt
  ∷ []

canonicalSensoryTransportNonPromotionCertificate :
  (transport : GeneralizedSensoryTransport) →
  SensoryTransportNonPromotionCertificate transport
canonicalSensoryTransportNonPromotionCertificate transport =
  record
    { boundaries =
        canonicalSensoryTransportNonPromotionBoundaries
    ; exactQualiaRecovery =
        false
    ; exactQualiaRecoveryIsFalse =
        refl
    ; arbitraryCrossSenseIdentity =
        false
    ; arbitraryCrossSenseIdentityIsFalse =
        refl
    ; theoremLevelBiologyClaimWithoutReceipts =
        false
    ; theoremLevelBiologyClaimWithoutReceiptsIsFalse =
        refl
    ; latentStateInjection =
        false
    ; latentStateInjectionIsFalse =
        refl
    ; boundaryReading =
        "The transport surface is quotient-only: no exact qualia recovery, no arbitrary cross-sense identity, and no theorem-level biology claim without external receipts."
    }

