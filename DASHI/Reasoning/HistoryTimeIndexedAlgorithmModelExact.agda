module DASHI.Reasoning.HistoryTimeIndexedAlgorithmModelExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- HISTORY/TIME-INDEXED ALGORITHM / MODEL IDENTITY
--
-- A live fibre may refine while the algorithm/model used to interrogate it is
-- held fixed.  Conversely, changing the algorithm/model is a separate governed
-- event and must not rewrite the earlier evidence path.
------------------------------------------------------------------------

record HistoryTimeAlgorithmModelSurface : Set₂ where
  constructor historyTimeAlgorithmModelSurface
  field
    History : Set
    Time : Set
    LiveState : Set
    AlgorithmModel : Set
    ModelVersion : Set

    liveStateAt : History → Time → LiveState
    modelAt : History → Time → AlgorithmModel
    modelVersionAt : History → Time → ModelVersion

    stateReference : String
    modelReference : String
    versionReference : String

open HistoryTimeAlgorithmModelSurface public

record StateRefinementWithFrozenModel
    (surface : HistoryTimeAlgorithmModelSurface)
    (history : History surface)
    (before after : Time surface) : Set₁ where
  constructor stateRefinementWithFrozenModel
  field
    modelUnchanged : modelAt surface history after ≡ modelAt surface history before
    modelVersionUnchanged :
      modelVersionAt surface history after ≡ modelVersionAt surface history before
    refinementReference : String

open StateRefinementWithFrozenModel public

record AlgorithmModelRevisionAuthority
    (surface : HistoryTimeAlgorithmModelSurface)
    (history : History surface)
    (before after : Time surface) : Set₁ where
  constructor algorithmModelRevisionAuthority
  field
    liveStateUnchanged : liveStateAt surface history after ≡ liveStateAt surface history before
    externalRevisionAuthority : String
    authorisedProvenance : String
    comparisonContractReference : String
    versionTransitionReference : String

open AlgorithmModelRevisionAuthority public

record ModelRelativeResult {Result : Set} (surface : HistoryTimeAlgorithmModelSurface) : Set₁ where
  constructor modelRelativeResult
  field
    history : History surface
    time : Time surface
    result : Result
    modelIdentity : AlgorithmModel surface
    modelVersion : ModelVersion surface
    modelMatchesPoint : modelIdentity ≡ modelAt surface history time
    versionMatchesPoint : modelVersion ≡ modelVersionAt surface history time
    resultReference : String

open ModelRelativeResult public

record ModelRevisionReaudit {Result : Set}
    (surface : HistoryTimeAlgorithmModelSurface)
    (history : History surface)
    (before after : Time surface) : Set₁ where
  constructor modelRevisionReaudit
  field
    authorisedRevision : AlgorithmModelRevisionAuthority surface history before after
    oldResult : ModelRelativeResult {Result} surface
    oldResultAtBefore : time oldResult ≡ before
    newResult : ModelRelativeResult {Result} surface
    newResultAtAfter : time newResult ≡ after
    reauditReference : String

open ModelRevisionReaudit public

record SameStateDifferentModelAt
    (surface : HistoryTimeAlgorithmModelSurface)
    (time : Time surface) : Set₁ where
  constructor sameStateDifferentModelAt
  field
    leftHistory rightHistory : History surface
    sameLiveState :
      liveStateAt surface leftHistory time ≡ liveStateAt surface rightHistory time
    modelsDiffer :
      modelAt surface leftHistory time ≡ modelAt surface rightHistory time → ⊥

open SameStateDifferentModelAt public

record HistoryTimeAlgorithmModelBoundary : Set where
  constructor historyTimeAlgorithmModelBoundary
  field
    stateRefinementMaySilentlyChangeModel : Bool
    stateRefinementMaySilentlyChangeModelIsFalse :
      stateRefinementMaySilentlyChangeModel ≡ false
    modelRevisionMayRewritePriorLiveState : Bool
    modelRevisionMayRewritePriorLiveStateIsFalse :
      modelRevisionMayRewritePriorLiveState ≡ false
    oldModelRelativeResultAutomaticallyTransfersToNewModel : Bool
    oldModelRelativeResultAutomaticallyTransfersToNewModelIsFalse :
      oldModelRelativeResultAutomaticallyTransfersToNewModel ≡ false
    sameLiveStateImpliesSameHistoryIndexedModel : Bool
    sameLiveStateImpliesSameHistoryIndexedModelIsFalse :
      sameLiveStateImpliesSameHistoryIndexedModel ≡ false

canonicalHistoryTimeAlgorithmModelBoundary : HistoryTimeAlgorithmModelBoundary
canonicalHistoryTimeAlgorithmModelBoundary =
  historyTimeAlgorithmModelBoundary
    false refl
    false refl
    false refl
    false refl
