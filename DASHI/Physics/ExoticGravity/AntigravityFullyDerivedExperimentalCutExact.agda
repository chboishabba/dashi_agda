module DASHI.Physics.ExoticGravity.AntigravityFullyDerivedExperimentalCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityResearchPromotionCutExact as Promotion
import DASHI.Physics.ExoticGravity.AntigravityExperimentalCutProvenanceExact as Provenance
import DASHI.Physics.ExoticGravity.AntigravityBundleExecutionDerivationExact as Derivation
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- FULLY DERIVED SAME-APPARATUS CUT
------------------------------------------------------------------------

record FullyDerivedSameApparatusExperimentalCut : Set where
  constructor fully-derived-same-apparatus-experimental-cut
  field
    provenancedCut : Provenance.ProvenancedSameApparatusExperimentalCut

    phaseProbeDerivation :
      Derivation.BundleExecutionDerivation
        (Provenance.phaseProbeExecution provenancedCut)
        (Promotion.phaseProbeBundle (Provenance.baseCut provenancedCut))

    ordinaryModelDerivation :
      Derivation.BundleExecutionDerivation
        (Provenance.ordinaryModelExecution provenancedCut)
        (Promotion.ordinaryModelBundle (Provenance.baseCut provenancedCut))

    scalingReplicationDerivation :
      Derivation.BundleExecutionDerivation
        (Provenance.scalingReplicationExecution provenancedCut)
        (Promotion.scalingReplicationBundle (Provenance.baseCut provenancedCut))

open FullyDerivedSameApparatusExperimentalCut public

record FullyDerivedComparativeAnomalyReceipt
    (claim : Anti.AntigravityClaim) : Set where
  constructor fully-derived-comparative-anomaly-receipt
  field
    experimentalCut : FullyDerivedSameApparatusExperimentalCut
    provenancedAnomaly : Provenance.ProvenancedComparativeAnomalyReceipt claim
    cutMatchesAnomaly :
      Provenance.experimentalCut provenancedAnomaly
        ≡ provenancedCut experimentalCut

open FullyDerivedComparativeAnomalyReceipt public

------------------------------------------------------------------------
-- Reverse residuals.
------------------------------------------------------------------------

data FullyDerivedCutResidual : Set where
  missingProvenancedCut : FullyDerivedCutResidual
  missingPhaseProbeDerivation : FullyDerivedCutResidual
  missingOrdinaryModelDerivation : FullyDerivedCutResidual
  missingScalingReplicationDerivation : FullyDerivedCutResidual
  missingFullyDerivedAnomalyIdentity : FullyDerivedCutResidual

producerForFullyDerivedCutResidual :
  FullyDerivedCutResidual → Search.ProducerClass
producerForFullyDerivedCutResidual missingProvenancedCut = Search.attributionProducer
producerForFullyDerivedCutResidual missingPhaseProbeDerivation = Search.identityProducer
producerForFullyDerivedCutResidual missingOrdinaryModelDerivation = Search.identityProducer
producerForFullyDerivedCutResidual missingScalingReplicationDerivation = Search.identityProducer
producerForFullyDerivedCutResidual missingFullyDerivedAnomalyIdentity = Search.identityProducer

data CurrentFullyDerivedCutAuthority : Set where

noCurrentFullyDerivedExperimentalCut :
  CurrentFullyDerivedCutAuthority → FullyDerivedSameApparatusExperimentalCut
noCurrentFullyDerivedExperimentalCut ()

record FullyDerivedExperimentalCutBoundary : Set where
  constructor fully-derived-experimental-cut-boundary
  field
    provenanceAloneProvesExecutionProducedBundle : Bool
    phaseProbeNeedsExactOutputDerivation : Bool
    ordinaryModelNeedsExactOutputDerivation : Bool
    scalingReplicationNeedsExactOutputDerivation : Bool
    fullyDerivedCutAutomaticallyProvesAntigravity : Bool
    fullyDerivedComparativeAnomalyStillRequiresPostComparisonWork : Bool

canonicalFullyDerivedExperimentalCutBoundary : FullyDerivedExperimentalCutBoundary
canonicalFullyDerivedExperimentalCutBoundary =
  fully-derived-experimental-cut-boundary false true true true false true
