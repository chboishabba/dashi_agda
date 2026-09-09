module DASHI.Physics.ExoticGravity.AntigravityExperimentalCutProvenanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityResearchPromotionCutExact as Promotion
import DASHI.Physics.ExoticGravity.AntigravitySourceBundleDerivationLineageExact as SourceDerivation
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- EXECUTION PROVENANCE FOR EACH SAME-APPARATUS BUNDLE
------------------------------------------------------------------------

record BundleExecutionProvenance : Set where
  constructor bundle-execution-provenance
  field
    responsibleBody : String
    apparatusCarrier : String
    runIdentifier : String
    rawDataCarrier : String
    rawDataHash : String
    dataRevision : String
    calibrationCarrier : String
    analysisImplementationCarrier : String
    analysisRevision : String
    exactResultLocator : String

open BundleExecutionProvenance public

record ProvenancedSameApparatusExperimentalCut : Set where
  constructor provenanced-same-apparatus-experimental-cut
  field
    baseCut : Promotion.SameApparatusExperimentalCut

    sourceReceipt : SourceDerivation.DerivedSourceAcquisitionReceipt
    sourceBundleMatches :
      SourceDerivation.compiledDerivedBundle sourceReceipt
        ≡ Promotion.sourceBundle baseCut

    sourceExecution : BundleExecutionProvenance
    phaseProbeExecution : BundleExecutionProvenance
    ordinaryModelExecution : BundleExecutionProvenance
    scalingReplicationExecution : BundleExecutionProvenance

    sourceApparatusMatches :
      apparatusCarrier sourceExecution ≡ Promotion.apparatusCarrier baseCut
    phaseApparatusMatches :
      apparatusCarrier phaseProbeExecution ≡ Promotion.apparatusCarrier baseCut
    ordinaryApparatusMatches :
      apparatusCarrier ordinaryModelExecution ≡ Promotion.apparatusCarrier baseCut
    scalingApparatusMatches :
      apparatusCarrier scalingReplicationExecution ≡ Promotion.apparatusCarrier baseCut

open ProvenancedSameApparatusExperimentalCut public

record ProvenancedComparativeAnomalyReceipt
    (claim : Anti.AntigravityClaim) : Set where
  constructor provenanced-comparative-anomaly-receipt
  field
    experimentalCut : ProvenancedSameApparatusExperimentalCut
    anomaly : Promotion.ComparativeAnomalyReceipt claim
    anomalyCutMatches :
      Promotion.experimentalCut anomaly ≡ baseCut experimentalCut

open ProvenancedComparativeAnomalyReceipt public

------------------------------------------------------------------------
-- Reverse residuals for the provenance-strengthened terminal cut.
------------------------------------------------------------------------

data ExperimentalCutProvenanceResidual : Set where
  missingSourceDerivationLineage : ExperimentalCutProvenanceResidual
  missingSourceExecutionProvenance : ExperimentalCutProvenanceResidual
  missingPhaseProbeExecutionProvenance : ExperimentalCutProvenanceResidual
  missingOrdinaryModelExecutionProvenance : ExperimentalCutProvenanceResidual
  missingScalingReplicationExecutionProvenance : ExperimentalCutProvenanceResidual
  missingSameApparatusExecutionBinding : ExperimentalCutProvenanceResidual
  missingAnomalyCutIdentity : ExperimentalCutProvenanceResidual

producerForExperimentalCutProvenanceResidual :
  ExperimentalCutProvenanceResidual → Search.ProducerClass
producerForExperimentalCutProvenanceResidual missingSourceDerivationLineage = Search.identityProducer
producerForExperimentalCutProvenanceResidual missingSourceExecutionProvenance = Search.attributionProducer
producerForExperimentalCutProvenanceResidual missingPhaseProbeExecutionProvenance = Search.attributionProducer
producerForExperimentalCutProvenanceResidual missingOrdinaryModelExecutionProvenance = Search.attributionProducer
producerForExperimentalCutProvenanceResidual missingScalingReplicationExecutionProvenance = Search.attributionProducer
producerForExperimentalCutProvenanceResidual missingSameApparatusExecutionBinding = Search.identityProducer
producerForExperimentalCutProvenanceResidual missingAnomalyCutIdentity = Search.identityProducer

------------------------------------------------------------------------
-- Current repo state remains uninhabited at the physical receipt level.
------------------------------------------------------------------------

data CurrentProvenancedExperimentalCutAuthority : Set where

noCurrentProvenancedExperimentalCut :
  CurrentProvenancedExperimentalCutAuthority → ProvenancedSameApparatusExperimentalCut
noCurrentProvenancedExperimentalCut ()

record ExperimentalCutProvenanceBoundary : Set where
  constructor experimental-cut-provenance-boundary
  field
    bundleStateWitnessAloneEqualsExecutionProvenance : Bool
    eachBundleNeedsRunDataHashRevision : Bool
    sourceBundleNeedsExactDataToBundleDerivation : Bool
    allBundleRunsMustBindSameApparatus : Bool
    baseComparativeAnomalyAutomaticallyCarriesTheseReceipts : Bool
    provenancedComparativeAnomalyStillEqualsUniversalAntigravityLaw : Bool

canonicalExperimentalCutProvenanceBoundary : ExperimentalCutProvenanceBoundary
canonicalExperimentalCutProvenanceBoundary =
  experimental-cut-provenance-boundary false true true true false false
