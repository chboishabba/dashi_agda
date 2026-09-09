module DASHI.Physics.ExoticGravity.AntigravityNegativeGPairedComparatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingBidiExact as NegativeG
import DASHI.Physics.GR.GravitationalPredictionObservationBidiExact as Pred
import DASHI.Physics.GR.GravitationalPredictionAttributionBidiExact as Attr
import DASHI.Physics.GR.NegativeGPredictionAuthorityExact as NegativeGAuthority
import DASHI.Physics.GR.SignedGSourceDynamicsBidiExact as SourceDynamics
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- +G GR VERSUS -G COUNTERFACTUAL: SAME-LAW / RE-SOLVED-SOURCE COMPARATOR
--
-- Prediction scope, observation channel, model law, propagation model and
-- detector response are welded.  The source model law is shared, but the
-- source trajectory/state must be solved separately under +G and -G.
------------------------------------------------------------------------

record SignedGPairedPrediction (claim : Anti.AntigravityClaim) : Set₁ where
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

    negativeAuthorityIsExactSignedGOwner :
      NegativeGAuthority.NegativeGInternalPredictionAuthority
        negativeGPrediction

    sameClaimScope :
      Pred.predictionClaimScope (Attr.prediction positiveGPrediction)
        ≡ Pred.predictionClaimScope (Attr.prediction negativeGPrediction)

    sameObservationChannel :
      Pred.channel (Attr.prediction positiveGPrediction)
        ≡ Pred.channel (Attr.prediction negativeGPrediction)

    sameObservable :
      Pred.observable (Attr.prediction positiveGPrediction)
        ≡ Pred.observable (Attr.prediction negativeGPrediction)

    sourceDynamicsPair :
      SourceDynamics.SignedGSourceDynamicsPair
        positiveGPrediction negativeGPrediction

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
  missingNegativeGExactSignedOwnerAuthority : SignedGComparatorResidual
  missingClaimScopeIdentity : SignedGComparatorResidual
  missingChannelIdentity : SignedGComparatorResidual
  missingObservableIdentity : SignedGComparatorResidual
  missingSignConditionedSourceDynamics : SignedGComparatorResidual
  missingPropagationModelIdentity : SignedGComparatorResidual
  missingDetectorResponseIdentity : SignedGComparatorResidual
  negativePredictionNotTypedModifiedGravity : SignedGComparatorResidual
  missingSignedResidualComparison : SignedGComparatorResidual

producerForSignedGComparatorResidual :
  SignedGComparatorResidual → Search.ProducerClass
producerForSignedGComparatorResidual missingPositiveGAttributedPrediction = Search.propositionSourceProducer
producerForSignedGComparatorResidual missingNegativeGAttributedPrediction = Search.propositionSourceProducer
producerForSignedGComparatorResidual missingNegativeGExactSignedOwnerAuthority = Search.attributionProducer
producerForSignedGComparatorResidual missingClaimScopeIdentity = Search.identityProducer
producerForSignedGComparatorResidual missingChannelIdentity = Search.identityProducer
producerForSignedGComparatorResidual missingObservableIdentity = Search.identityProducer
producerForSignedGComparatorResidual missingSignConditionedSourceDynamics = Search.propositionSourceProducer
producerForSignedGComparatorResidual missingPropagationModelIdentity = Search.identityProducer
producerForSignedGComparatorResidual missingDetectorResponseIdentity = Search.identityProducer
producerForSignedGComparatorResidual negativePredictionNotTypedModifiedGravity = Search.discriminatorProducer
producerForSignedGComparatorResidual missingSignedResidualComparison = Search.contradictionProducer

record SignedGPairedComparatorBoundary : Set where
  constructor signed-g-paired-comparator-boundary
  field
    positiveAndNegativePredictionsMayUseDifferentSourceModelLaws : Bool
    sameSourceModelMeansSameSolvedSourceState : Bool
    signConditionedSourceSolutionRequired : Bool
    positiveAndNegativePredictionsMayUseDifferentClaimScopes : Bool
    positiveAndNegativePredictionsMayUseDifferentDetectorModels : Bool
    negativeGAlternativeMustBeTypedNonGR : Bool
    arbitraryInternalTheoremMayAuthorizeNegativeGPrediction : Bool
    exactSignedGOwnerAuthorityRequired : Bool
    sameLawReSolvedSourcePairIsolatesCouplingSignBetterThanUnpairedComparison : Bool
    betterNegativeGFitAutomaticallyEstablishesNegativeGPhysics : Bool
    betterNegativeGFitAutomaticallyProvesAntigravity : Bool

canonicalSignedGPairedComparatorBoundary : SignedGPairedComparatorBoundary
canonicalSignedGPairedComparatorBoundary =
  signed-g-paired-comparator-boundary
    false false true false false true false true true false false
