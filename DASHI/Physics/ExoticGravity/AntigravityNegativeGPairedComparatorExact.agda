module DASHI.Physics.ExoticGravity.AntigravityNegativeGPairedComparatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingBidiExact as NegativeG
import DASHI.Physics.GR.GravitationalPredictionObservationBidiExact as Pred
import DASHI.Physics.GR.GravitationalPredictionAttributionBidiExact as Attr
import DASHI.Physics.GR.GravitationalEpistemicLineageExact as Lineage
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- +G GR VERSUS -G COUNTERFACTUAL: SAME-INPUT PAIRED COMPARATOR
--
-- The only intended theory coordinate to vary is the gravitational coupling
-- sign.  Prediction scope, observation channel, source model, propagation model
-- and detector response must remain welded.  Otherwise a better fit cannot be
-- attributed to the sign coordinate.
--
-- The -G branch constructed in this repo is a DASHI counterfactual theorem
-- carrier, not an externally sourced claim that G is physically negative.
------------------------------------------------------------------------

data IsInternalPredictionAuthority : Attr.PredictionAuthority → Set where
  internal-prediction-authority :
    (lineage : Lineage.InternalTheoremProofLineage) →
    IsInternalPredictionAuthority (Attr.internalTheoremAuthority lineage)

record SignedGPairedPrediction (claim : Anti.AntigravityClaim) : Set where
  constructor signed-g-paired-prediction
  field
    claimProbe : NegativeG.NegativeGClaimProbe claim

    positiveGPrediction : Attr.AttributedGravitationalPrediction
    negativeGPrediction : Attr.AttributedGravitationalPrediction

    positiveFamilyIsGR :
      Pred.theoryFamily (Attr.prediction positiveGPrediction)
        ≡ Pred.generalRelativityTheory

    negativeFamilyIsModifiedGravity :
      Pred.theoryFamily (Attr.prediction negativeGPrediction)
        ≡ Pred.modifiedGravityTheory

    negativeAuthorityIsInternalProofLineage :
      IsInternalPredictionAuthority (Attr.authority negativeGPrediction)

    sameClaimScope :
      Pred.predictionClaimScope (Attr.prediction positiveGPrediction)
        ≡ Pred.predictionClaimScope (Attr.prediction negativeGPrediction)

    sameObservationChannel :
      Pred.channel (Attr.prediction positiveGPrediction)
        ≡ Pred.channel (Attr.prediction negativeGPrediction)

    sameObservable :
      Pred.observable (Attr.prediction positiveGPrediction)
        ≡ Pred.observable (Attr.prediction negativeGPrediction)

    sameSourceModel :
      Pred.sourceModelCarrier (Attr.prediction positiveGPrediction)
        ≡ Pred.sourceModelCarrier (Attr.prediction negativeGPrediction)

    samePropagationModel :
      Pred.propagationModelCarrier (Attr.prediction positiveGPrediction)
        ≡ Pred.propagationModelCarrier (Attr.prediction negativeGPrediction)

    sameDetectorResponse :
      Pred.detectorResponseCarrier (Attr.prediction positiveGPrediction)
        ≡ Pred.detectorResponseCarrier (Attr.prediction negativeGPrediction)

open SignedGPairedPrediction public

------------------------------------------------------------------------
-- REVERSE RESIDUALS
------------------------------------------------------------------------

data SignedGComparatorResidual : Set where
  missingPositiveGAttributedPrediction : SignedGComparatorResidual
  missingNegativeGAttributedPrediction : SignedGComparatorResidual
  missingNegativeGInternalProofLineage : SignedGComparatorResidual
  missingClaimScopeIdentity : SignedGComparatorResidual
  missingChannelIdentity : SignedGComparatorResidual
  missingObservableIdentity : SignedGComparatorResidual
  missingSourceModelIdentity : SignedGComparatorResidual
  missingPropagationModelIdentity : SignedGComparatorResidual
  missingDetectorResponseIdentity : SignedGComparatorResidual
  negativePredictionNotTypedModifiedGravity : SignedGComparatorResidual
  missingSignedResidualComparison : SignedGComparatorResidual

producerForSignedGComparatorResidual :
  SignedGComparatorResidual → Search.ProducerClass
producerForSignedGComparatorResidual missingPositiveGAttributedPrediction = Search.propositionSourceProducer
producerForSignedGComparatorResidual missingNegativeGAttributedPrediction = Search.propositionSourceProducer
producerForSignedGComparatorResidual missingNegativeGInternalProofLineage = Search.attributionProducer
producerForSignedGComparatorResidual missingClaimScopeIdentity = Search.identityProducer
producerForSignedGComparatorResidual missingChannelIdentity = Search.identityProducer
producerForSignedGComparatorResidual missingObservableIdentity = Search.identityProducer
producerForSignedGComparatorResidual missingSourceModelIdentity = Search.identityProducer
producerForSignedGComparatorResidual missingPropagationModelIdentity = Search.identityProducer
producerForSignedGComparatorResidual missingDetectorResponseIdentity = Search.identityProducer
producerForSignedGComparatorResidual negativePredictionNotTypedModifiedGravity = Search.discriminatorProducer
producerForSignedGComparatorResidual missingSignedResidualComparison = Search.contradictionProducer

record SignedGPairedComparatorBoundary : Set where
  constructor signed-g-paired-comparator-boundary
  field
    positiveAndNegativePredictionsMayUseDifferentSources : Bool
    positiveAndNegativePredictionsMayUseDifferentClaimScopes : Bool
    positiveAndNegativePredictionsMayUseDifferentDetectorModels : Bool
    negativeGAlternativeMustBeTypedNonGR : Bool
    negativeGCounterfactualMayUseExternalSourceAuthority : Bool
    negativeGCounterfactualRequiresInternalProofLineage : Bool
    sameInputPairIsolatesCouplingSignBetterThanUnpairedComparison : Bool
    betterNegativeGFitAutomaticallyEstablishesNegativeGPhysics : Bool
    betterNegativeGFitAutomaticallyProvesAntigravity : Bool

canonicalSignedGPairedComparatorBoundary : SignedGPairedComparatorBoundary
canonicalSignedGPairedComparatorBoundary =
  signed-g-paired-comparator-boundary
    false false false true false true true false false
