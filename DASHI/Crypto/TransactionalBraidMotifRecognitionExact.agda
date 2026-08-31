module DASHI.Crypto.TransactionalBraidMotifRecognitionExact where

open import DASHI.Core.Prelude

import DASHI.Core.ActionCrossingTraceCalculusExact as Trace
import DASHI.Core.ActionCrossingMotifExact as Motif

------------------------------------------------------------------------
-- DEFENSIVE TRANSACTIONAL MOTIF RECOGNITION
--
-- This specializes the generic action-crossing motifs to asset-provenance
-- review.  It recognizes abstract trace shapes only; it provides no procedure
-- for concealment, laundering, evasion, or defeating tracing/disclosure.
------------------------------------------------------------------------

data Asset : Set where
  origin relay sink : Asset

data AssetAction : Set where
  transferAction splitAction mergeAction returnAction : AssetAction

originToRelay : AssetAction → Trace.CrossingEvent Asset AssetAction
originToRelay action = Trace.crossing-event origin relay action

relayToOrigin : AssetAction → Trace.CrossingEvent Asset AssetAction
relayToOrigin action = Trace.crossing-event relay origin action

relayToSink : AssetAction → Trace.CrossingEvent Asset AssetAction
relayToSink action = Trace.crossing-event relay sink action

originToSink : AssetAction → Trace.CrossingEvent Asset AssetAction
originToSink action = Trace.crossing-event origin sink action

washLikeReturnTrace : Trace.ActionTrace Asset AssetAction
washLikeReturnTrace =
  originToRelay transferAction ∷ relayToOrigin returnAction ∷ []

peelLikeRelayTrace : Trace.ActionTrace Asset AssetAction
peelLikeRelayTrace =
  originToRelay transferAction ∷ relayToSink transferAction ∷ []

splitLikeTrace : Trace.ActionTrace Asset AssetAction
splitLikeTrace =
  originToRelay splitAction ∷ originToSink splitAction ∷ []

mergeLikeTrace : Trace.ActionTrace Asset AssetAction
mergeLikeTrace =
  originToSink mergeAction ∷ relayToSink mergeAction ∷ []

washLikeReturnMotif : Motif.ReturnCycleMotif washLikeReturnTrace
washLikeReturnMotif =
  Motif.return-cycle-motif
    (originToRelay transferAction)
    (relayToOrigin returnAction)
    refl refl refl

peelLikeRelayMotif : Motif.RelayMotif peelLikeRelayTrace
peelLikeRelayMotif =
  Motif.relay-motif
    (originToRelay transferAction)
    (relayToSink transferAction)
    refl refl

splitLikeMotif : Motif.SplitMotif splitLikeTrace
splitLikeMotif =
  Motif.split-motif
    (originToRelay splitAction)
    (originToSink splitAction)
    refl refl

mergeLikeMotif : Motif.MergeMotif mergeLikeTrace
mergeLikeMotif =
  Motif.merge-motif
    (originToSink mergeAction)
    (relayToSink mergeAction)
    refl refl

------------------------------------------------------------------------
-- Motif support graphs erase action labels but retain interacting asset pairs.
------------------------------------------------------------------------

washSupportGraph = Motif.supportGraph washLikeReturnTrace
peelSupportGraph = Motif.supportGraph peelLikeRelayTrace
splitSupportGraph = Motif.supportGraph splitLikeTrace
mergeSupportGraph = Motif.supportGraph mergeLikeTrace

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data WashMotifProvesConcealmentIntent : Set where
data PeelMotifProvesConcealmentIntent : Set where
data ReturnCycleIsAlwaysWashTrading : Set where
data RelayIsAlwaysAssetObfuscation : Set where
data MotifRecognitionIsLegalConclusion : Set where
data MotifRecognitionProvidesConcealmentProcedure : Set where

washMotifDoesNotProveConcealmentIntent : WashMotifProvesConcealmentIntent → ⊥
washMotifDoesNotProveConcealmentIntent ()

peelMotifDoesNotProveConcealmentIntent : PeelMotifProvesConcealmentIntent → ⊥
peelMotifDoesNotProveConcealmentIntent ()

returnCycleIsNotAlwaysWashTrading : ReturnCycleIsAlwaysWashTrading → ⊥
returnCycleIsNotAlwaysWashTrading ()

relayIsNotAlwaysAssetObfuscation : RelayIsAlwaysAssetObfuscation → ⊥
relayIsNotAlwaysAssetObfuscation ()

motifRecognitionDoesNotCreateLegalConclusion : MotifRecognitionIsLegalConclusion → ⊥
motifRecognitionDoesNotCreateLegalConclusion ()

motifRecognitionDoesNotProvideConcealmentProcedure :
  MotifRecognitionProvidesConcealmentProcedure → ⊥
motifRecognitionDoesNotProvideConcealmentProcedure ()

record TransactionalBraidMotifRecognitionBoundary : Set where
  constructor transactional-braid-motif-recognition-boundary
  field
    washLikeReturnMotifRecognized : Bool
    peelLikeRelayMotifRecognized : Bool
    splitMotifRecognized : Bool
    mergeMotifRecognized : Bool
    supportGraphAvailable : Bool
    motifProvesIntent : Bool
    motifCreatesLegalConclusion : Bool
    concealmentProcedureProvided : Bool

canonicalTransactionalBraidMotifRecognitionBoundary :
  TransactionalBraidMotifRecognitionBoundary
canonicalTransactionalBraidMotifRecognitionBoundary =
  transactional-braid-motif-recognition-boundary
    true true true true true false false false
