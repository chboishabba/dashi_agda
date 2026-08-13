module DASHI.Cognition.PNF.LLMCompressionAccessibilityDefectsExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.MultiResolutionAttentionFutureSufficiencyExact as Multi

------------------------------------------------------------------------
-- Finite context world.
------------------------------------------------------------------------

data Query : Set where
  askRemote askLocal : Query

record FineContext : Set where
  constructor fineContext
  field
    remoteCritical : Bool
    localCritical : Bool
    remoteNoise : Bool

open FineContext public

observeFine : Query → FineContext → Bool
observeFine askRemote context = remoteCritical context
observeFine askLocal context = localCritical context

leftContext : FineContext
leftContext = fineContext false true false

rightContext : FineContext
rightContext = fineContext true true false

remoteFineObservationsDiffer :
  observeFine askRemote leftContext ≡ observeFine askRemote rightContext → ⊥
remoteFineObservationsDiffer ()

------------------------------------------------------------------------
-- Failure mode 1: compression loss.  The global compressor has already erased
-- the remote-critical bit, so no later selector can recover it.
------------------------------------------------------------------------

compressLossy : FineContext → Bool
compressLossy context = remoteNoise context

lossyCompressionCollides :
  compressLossy leftContext ≡ compressLossy rightContext
lossyCompressionCollides = refl

record CompressionLossWitness : Set where
  constructor compressionLossWitness
  field
    left right : FineContext
    sameCompressedCarrier : compressLossy left ≡ compressLossy right
    futureQuery : Query
    fineObservationDiffers :
      observeFine futureQuery left ≡ observeFine futureQuery right → ⊥

compressionLossIsReal : CompressionLossWitness
compressionLossIsReal =
  compressionLossWitness
    leftContext rightContext refl askRemote remoteFineObservationsDiffer

------------------------------------------------------------------------
-- Failure mode 2: accessibility loss.  Compression still retains the critical
-- remote coordinate, but the query selector chooses only the noise coordinate.
------------------------------------------------------------------------

record CompressedGlobal : Set where
  constructor compressedGlobal
  field
    retainedRemote : Bool
    retainedNoise : Bool

open CompressedGlobal public

compressRetainingRemote : FineContext → CompressedGlobal
compressRetainingRemote context =
  compressedGlobal (remoteCritical context) (remoteNoise context)

wrongSelector : Query → CompressedGlobal → Bool
wrongSelector askRemote compressed = retainedNoise compressed
wrongSelector askLocal compressed = retainedNoise compressed

remoteIsStillRepresented :
  compressRetainingRemote leftContext ≡ compressRetainingRemote rightContext → ⊥
remoteIsStillRepresented ()

wrongSelectorHidesRepresentedDifference :
  wrongSelector askRemote (compressRetainingRemote leftContext)
  ≡ wrongSelector askRemote (compressRetainingRemote rightContext)
wrongSelectorHidesRepresentedDifference = refl

accessibilityLossWithoutRepresentationLoss :
  Multi.RepresentedButInaccessible compressRetainingRemote wrongSelector
accessibilityLossWithoutRepresentationLoss =
  Multi.representedButInaccessible
    leftContext
    rightContext
    askRemote
    remoteIsStillRepresented
    wrongSelectorHidesRepresentedDifference

------------------------------------------------------------------------
-- Positive construction: coarse global remote information plus fine local
-- residual exactly answers every query in this finite consumer family.
------------------------------------------------------------------------

compressRemote : FineContext → Bool
compressRemote context = remoteCritical context

selectRemote : Query → Bool → Bool
selectRemote query compressed = compressed

localResidual : FineContext → Bool
localResidual context = localCritical context

observeRetained : Query → Bool → Bool → Bool
observeRetained askRemote selected local = selected
observeRetained askLocal selected local = local

multiResolutionSystem :
  Multi.MultiResolutionConsumerSystem
    FineContext Bool Bool Bool Query Bool
multiResolutionSystem =
  Multi.multiResolutionConsumerSystem
    compressRemote
    selectRemote
    localResidual
    observeFine
    observeRetained
    factor
  where
    factor :
      (query : Query) → (context : FineContext) →
      observeFine query context
      ≡ observeRetained query
          (selectRemote query (compressRemote context))
          (localResidual context)
    factor askRemote (fineContext remote local noise) = refl
    factor askLocal (fineContext remote local noise) = refl

multiResolutionCarrierIsFutureSufficient :
  Multi.MultiResolutionFutureSufficient multiResolutionSystem
multiResolutionCarrierIsFutureSufficient =
  Multi.factorizationCertifiesMultiResolutionFutureSufficiency
    multiResolutionSystem

------------------------------------------------------------------------
-- The two defect types are therefore logically distinct:
--   compression loss: distinction absent from retained global carrier;
--   accessibility loss: distinction retained but not selected for the query.
------------------------------------------------------------------------
