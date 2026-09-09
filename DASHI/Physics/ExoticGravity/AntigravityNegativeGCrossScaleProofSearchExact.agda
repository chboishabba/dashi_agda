module DASHI.Physics.ExoticGravity.AntigravityNegativeGCrossScaleProofSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as Signed
import DASHI.Physics.GR.SignedNewtonianLimitBidiExact as Newton
import DASHI.Physics.GR.UniversalSignedGCrossScaleFingerprintBidiExact as Universal
import DASHI.Physics.GR.NegativeGGravitationalWaveTestRoutingExact as WaveRoute
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- UNIVERSAL NEGATIVE-G PROOF SEARCH
--
-- A local repulsive anomaly is insufficient for a universal sign claim.  The
-- same negative coupling sign must survive independent local, wave-source, and
-- cosmological consumers.  This owner only schedules those residuals.
------------------------------------------------------------------------

data NegativeGCrossScaleResidual : Set where
  missingLocalPositiveDensityResponse : NegativeGCrossScaleResidual
  missingSameSourceSignReceipt : NegativeGCrossScaleResidual
  missingSelfConsistentNegativeGWeakFieldSolution : NegativeGCrossScaleResidual
  missingNegativeGWaveSourceDynamics : NegativeGCrossScaleResidual
  missingNegativeGCosmologicalDynamics : NegativeGCrossScaleResidual
  missingCrossScaleSameSignIdentity : NegativeGCrossScaleResidual
  missingCrossScaleAttributionLineage : NegativeGCrossScaleResidual
  crossScaleContradictionOpen : NegativeGCrossScaleResidual

producerForNegativeGCrossScaleResidual :
  NegativeGCrossScaleResidual → Search.ProducerClass
producerForNegativeGCrossScaleResidual missingLocalPositiveDensityResponse =
  Search.empiricalEvidenceProducer
producerForNegativeGCrossScaleResidual missingSameSourceSignReceipt =
  Search.identityProducer
producerForNegativeGCrossScaleResidual missingSelfConsistentNegativeGWeakFieldSolution =
  Search.propositionSourceProducer
producerForNegativeGCrossScaleResidual missingNegativeGWaveSourceDynamics =
  Search.propositionSourceProducer
producerForNegativeGCrossScaleResidual missingNegativeGCosmologicalDynamics =
  Search.propositionSourceProducer
producerForNegativeGCrossScaleResidual missingCrossScaleSameSignIdentity =
  Search.identityProducer
producerForNegativeGCrossScaleResidual missingCrossScaleAttributionLineage =
  Search.attributionProducer
producerForNegativeGCrossScaleResidual crossScaleContradictionOpen =
  Search.contradictionProducer

------------------------------------------------------------------------
-- Highest-alpha local discriminator.
--
-- This is an interface for a real calibrated observation.  No canonical
-- inhabitant is supplied here.
------------------------------------------------------------------------

record PositiveDensityAttractionReceipt : Set where
  constructor positive-density-attraction-receipt
  field
    apparatusCarrier : String
    sourceDensityCarrier : String
    positiveDensityReceipt : String
    calibratedObservationCarrier : String
    observedResponse : Newton.RadialResponseOrientation
    observedAttractive :
      observedResponse ≡ Newton.attractiveTowardPositiveSource

open PositiveDensityAttractionReceipt public

negativeGPositiveDensityPrediction : Newton.RadialResponseOrientation
negativeGPositiveDensityPrediction =
  Newton.positiveDensityRadialResponse Signed.negativeCoupling

negativeGPredictionIsRepulsive :
  negativeGPositiveDensityPrediction ≡ Newton.repulsiveAwayFromPositiveSource
negativeGPredictionIsRepulsive = refl

attractivePositiveDensityReceiptRejectsFrozenNegativeGResponse :
  (receipt : PositiveDensityAttractionReceipt) →
  negativeGPositiveDensityPrediction ≡ observedResponse receipt → ⊥
attractivePositiveDensityReceiptRejectsFrozenNegativeGResponse receipt equality
  rewrite observedAttractive receipt = equality
  where
    impossible :
      Newton.repulsiveAwayFromPositiveSource
        ≡ Newton.attractiveTowardPositiveSource → ⊥
    impossible ()

------------------------------------------------------------------------
-- Search priority.  Local sign discrimination is cheaper and more direct than
-- solving a complete negative-G compact-binary population or cosmology.
------------------------------------------------------------------------

data NegativeGSearchStage : Set where
  localSignDiscriminatorStage : NegativeGSearchStage
  selfConsistentWeakFieldStage : NegativeGSearchStage
  waveSourceDynamicsStage : NegativeGSearchStage
  cosmologicalDynamicsStage : NegativeGSearchStage
  crossScaleIdentityStage : NegativeGSearchStage
  contradictionAssessmentStage : NegativeGSearchStage

firstUniversalNegativeGStage : NegativeGSearchStage
firstUniversalNegativeGStage = localSignDiscriminatorStage

record NegativeGCrossScaleProofSearchBoundary : Set where
  constructor negative-g-cross-scale-proof-search-boundary
  field
    localRepulsiveAnomalyPaysUniversalNegativeG : Bool
    positiveDensityAttractionCanDiscriminateFrozenNegativeGSign : Bool
    localSignTestAloneConstructsFullNegativeGTheory : Bool
    vacuumGWPropagationAlonePaysNegativeGSourceDynamics : Bool
    cosmologyMayBeSkippedAfterLocalAnomaly : Bool
    sameSignAcrossScalesRequiresIdentityReceipt : Bool
    crossScaleContradictionMayRejectUniversalNegativeG : Bool
    rejectionOfUniversalNegativeGRejectsEveryLocalEffectiveRepulsionModel : Bool

canonicalNegativeGCrossScaleProofSearchBoundary : NegativeGCrossScaleProofSearchBoundary
canonicalNegativeGCrossScaleProofSearchBoundary =
  negative-g-cross-scale-proof-search-boundary
    false true false false false true true false

existingUniversalBoundary : Universal.UniversalSignedGCrossScaleBoundary
existingUniversalBoundary = Universal.canonicalUniversalSignedGCrossScaleBoundary

existingWaveRoutingBoundary : WaveRoute.NegativeGWaveTestBoundary
existingWaveRoutingBoundary = WaveRoute.canonicalNegativeGWaveTestBoundary
