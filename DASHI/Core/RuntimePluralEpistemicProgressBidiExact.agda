module DASHI.Core.RuntimePluralEpistemicProgressBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.BraidedRuntimeProofProvenanceBidiExact as Runtime
import DASHI.Core.PluralEpistemicProgressMethodologyBidiExact as Method
import DASHI.Core.PairIndexedInformationLossLocusBidiExact as Loss
import DASHI.Core.ProvenanceQuorumAdequacyBidiExact as Quorum
import DASHI.Core.ProvenanceSensitiveConsumerAdequacyBidiExact as Provenance

runtimeCorrectionAppendsHistory :
  Runtime.correctionAppendsHistoryRatherThanRewritesIt
    Runtime.canonicalBraidedRuntimeProofBoundary ≡ true
runtimeCorrectionAppendsHistory = refl

runtimeSameProcessNeedsCommutingProjection :
  Runtime.sameProcessNeedsCommutingProjection
    Runtime.canonicalBraidedRuntimeProofBoundary ≡ true
runtimeSameProcessNeedsCommutingProjection = refl

coarseViewCannotRecoverCollapsedPair :
  Loss.toyDownstream (Loss.toyObserve Loss.x)
  ≡ Loss.toyDownstream (Loss.toyObserve Loss.y)
coarseViewCannotRecoverCollapsedPair = Loss.toyCollapsedPairNeverRestored

repeatedEvidenceStillNeedsRootIndependence :
  Quorum.IndependentProvenanceQuorumTwo
    Provenance.toyPolicy Provenance.targetConsumer
    Provenance.firstReport Provenance.secondReport → ⊥
repeatedEvidenceStillNeedsRootIndependence =
  Quorum.toyHeadcountDoesNotCreateIndependentQuorum

runtimeMayClarifyProvenance : Method.EpistemicProgressRoute
runtimeMayClarifyProvenance = Method.establishIndependentProvenance

runtimeMayNeedNewCoordinate : Method.EpistemicProgressRoute
runtimeMayNeedNewCoordinate = Method.addNewCoordinate

data EventMultiplicityCreatesIndependentCorroboration : Set where
data ReplayRestoresFineHistoryFromCollapsedView : Set where
data RuntimeCorrectionMayRewritePriorProvenance : Set where

eventMultiplicityDoesNotCreateIndependentCorroboration : EventMultiplicityCreatesIndependentCorroboration → ⊥
eventMultiplicityDoesNotCreateIndependentCorroboration ()

replayDoesNotRestoreFineHistoryFromCollapsedView : ReplayRestoresFineHistoryFromCollapsedView → ⊥
replayDoesNotRestoreFineHistoryFromCollapsedView ()

runtimeCorrectionDoesNotRewritePriorProvenance : RuntimeCorrectionMayRewritePriorProvenance → ⊥
runtimeCorrectionDoesNotRewritePriorProvenance ()

record RuntimePluralEpistemicBoundary : Set where
  constructor runtime-plural-epistemic-boundary
  field
    correctionIsAppendOnly : Bool
    provenanceStrandsRemainDistinct : Bool
    eventCountCreatesIndependentSupport : Bool
    deterministicReplayRestoresErasedFineDistinction : Bool
    addedObservationMayBeRequired : Bool
    runtimeProgressCreatesProofTruth : Bool

canonicalRuntimePluralEpistemicBoundary : RuntimePluralEpistemicBoundary
canonicalRuntimePluralEpistemicBoundary =
  runtime-plural-epistemic-boundary true true false false true false
