module DASHI.Biology.EvolvedSensoryTransport where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.Closure.SensoryAttractorClasses

------------------------------------------------------------------------
-- Biology-facing receipt for generalized sensory transport.
--
-- The module packages the reusable physics/closure attractor surface as a
-- biological claim boundary.  It formalizes a pipeline from world physics to
-- evolutionary retention, but keeps all subjective and cross-modality claims
-- behind explicit non-promotion certificates.

data BiologicalSensoryDomain : Set where
  photicDomain : BiologicalSensoryDomain
  acousticDomain : BiologicalSensoryDomain
  chemicalDomain : BiologicalSensoryDomain
  magneticDomain : BiologicalSensoryDomain
  mechanicalDomain : BiologicalSensoryDomain
  thermalDomain : BiologicalSensoryDomain
  bodyInternalDomain : BiologicalSensoryDomain
  multimodalDomain : BiologicalSensoryDomain

data SensoryReceiptStatus : Set where
  receiptSurfaceOnly : SensoryReceiptStatus
  measurementBackedInstanceRequired : SensoryReceiptStatus
  retainedAsQuotientClassOnly : SensoryReceiptStatus

record SensoryAttractorRetentionSurface
    (transport : GeneralizedSensoryTransport)
    (evolved : EvolvedLowDimensionalSensoryAttractor transport) : Set₁ where
  field
    PopulationSample : Set
    DevelopmentalHistory : Set
    EcologicalContext : Set
    MeasurementReceipt : Set

    sampleLineage :
      PopulationSample →
      EvolutionaryLineage transport

    developmentalContext :
      PopulationSample →
      DevelopmentalHistory

    ecologicalContext :
      PopulationSample →
      EcologicalContext

    measurementReceiptFor :
      PopulationSample →
      MeasurementReceipt

    retainedInSample :
      (sample : PopulationSample) →
      EvolutionaryRetentionCriterion →
      Set

    retentionRequiresReceipt :
      (sample : PopulationSample) →
      retainedInSample sample environmentalRobustnessImproves →
      MeasurementReceipt

    retentionSurfaceReading :
      String

open SensoryAttractorRetentionSurface public

record EvolvedSensoryTransportReceipt : Set₁ where
  field
    transport :
      GeneralizedSensoryTransport

    evolvedAttractor :
      EvolvedLowDimensionalSensoryAttractor transport

    retentionSurface :
      SensoryAttractorRetentionSurface transport evolvedAttractor

    biologicalDomains :
      List BiologicalSensoryDomain

    transportPipeline :
      List SensoryTransportLayer

    status :
      SensoryReceiptStatus

    nonPromotionCertificate :
      SensoryTransportNonPromotionCertificate transport

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

    allowedClaim :
      List String

    forbiddenClaim :
      List String

    receiptReading :
      String

open EvolvedSensoryTransportReceipt public

record EvolvedSensoryTransportPipelineWitness
    (receipt : EvolvedSensoryTransportReceipt) : Set where
  field
    pipelineIsWorldToRetention :
      transportPipeline receipt ≡ defaultSensoryTransportPipeline

    nonPromotionBoundariesPresent :
      boundaries (nonPromotionCertificate receipt) ≡
      canonicalSensoryTransportNonPromotionBoundaries

    qualiaRecoveryBlocked :
      exactQualiaRecovery receipt ≡ false

    crossSenseIdentityBlocked :
      arbitraryCrossSenseIdentity receipt ≡ false

    unsupportedBiologyTheoremBlocked :
      theoremLevelBiologyClaimWithoutReceipts receipt ≡ false

    witnessReading :
      String

open EvolvedSensoryTransportPipelineWitness public

record SensoryBehaviorQuotientRetention
    (receipt : EvolvedSensoryTransportReceipt) : Set₁ where
  field
    world :
      WorldPhysics (transport receipt)

    environment :
      Environment (transport receipt)

    bodyState :
      ConnectomeBodyState (transport receipt)

    lineage :
      EvolutionaryLineage (transport receipt)

    quotientClass :
      PerceptualBehaviorClass (transport receipt)

    quotientMatchesPipeline :
      samePerceptualBehaviorClass (transport receipt)
        quotientClass
        (sensoryPipelineFromWorld
          (transport receipt)
          world
          environment
          bodyState)

    fitnessSignal :
      FitnessSignal (transport receipt)

    fitnessMatchesPipeline :
      fitnessSignal ≡
      sensoryRetentionSignalFromWorld
        (transport receipt)
        world
        environment
        bodyState
        lineage

    retainedOnlyAsCriterion :
      EvolutionaryRetentionCriterion →
      Set

    quotientReading :
      String

open SensoryBehaviorQuotientRetention public

safeEvolvedSensoryTransportPipelineWitness :
  (receipt : EvolvedSensoryTransportReceipt) →
  transportPipeline receipt ≡ defaultSensoryTransportPipeline →
  boundaries (nonPromotionCertificate receipt) ≡
  canonicalSensoryTransportNonPromotionBoundaries →
  EvolvedSensoryTransportPipelineWitness receipt
safeEvolvedSensoryTransportPipelineWitness
  receipt
  pipelineProof
  boundaryProof =
  record
    { pipelineIsWorldToRetention =
        pipelineProof
    ; nonPromotionBoundariesPresent =
        boundaryProof
    ; qualiaRecoveryBlocked =
        exactQualiaRecoveryIsFalse receipt
    ; crossSenseIdentityBlocked =
        arbitraryCrossSenseIdentityIsFalse receipt
    ; unsupportedBiologyTheoremBlocked =
        theoremLevelBiologyClaimWithoutReceiptsIsFalse receipt
    ; witnessReading =
        "The receipt follows the world-physics to evolutionary-retention pipeline and keeps qualia, arbitrary cross-sense identity, and unsupported biological theorem claims blocked."
    }

