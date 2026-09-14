module DASHI.ComputerScience.RSA260MultipartReconstructionSpineExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.MultipartSameObjectReconstructionExact as Multipart
import DASHI.ComputerScience.RSA260369DNA27CodecNDimTetrationCrossPollinationExact as RSA

------------------------------------------------------------------------
-- RSA-260 -> canonical multipart same-object reconstruction spine.
--
-- The RSA owner already records the exact production-manifest obligations:
-- local chunk digest, chunk position, seam compatibility, global
-- reconstruction, global same-object digest, explicit tails, and prohibition
-- on paying a conclusion while a chunk is missing.
--
-- This adapter does not manufacture production bytes or an inhabited
-- CompleteMultipartReconstruction.  It only proves that the existing RSA
-- requirement surface is an instance of the canonical multipart discipline.
------------------------------------------------------------------------

rsa260LocalChunkDigestRequired :
  RSA.localChunkDigestRequired RSA.currentArtifactManifestBoundary ≡ true
rsa260LocalChunkDigestRequired = refl

rsa260ChunkPositionRequired :
  RSA.chunkPositionRequired RSA.currentArtifactManifestBoundary ≡ true
rsa260ChunkPositionRequired = refl

rsa260SeamCompatibilityRequired :
  RSA.seamBoundaryCompatibilityRequired RSA.currentArtifactManifestBoundary ≡ true
rsa260SeamCompatibilityRequired = refl

rsa260GlobalReconstructionReceiptRequired :
  RSA.globalReconstructionReceiptRequired RSA.currentArtifactManifestBoundary ≡ true
rsa260GlobalReconstructionReceiptRequired = refl

rsa260GlobalSameObjectDigestRequired :
  RSA.globalSameObjectDigestRequired RSA.currentArtifactManifestBoundary ≡ true
rsa260GlobalSameObjectDigestRequired = refl

rsa260MissingChunkCannotPayWhole :
  RSA.conclusionPaymentMayIgnoreMissingChunk RSA.currentArtifactManifestBoundary ≡ false
rsa260MissingChunkCannotPayWhole = refl

rsa260CompleteMultipartReconstructionStillUnpaid :
  RSA.sameObjectChunkManifestPaid RSA.currentRSA260369DNA27RoadmapBoundary ≡ false
rsa260CompleteMultipartReconstructionStillUnpaid = refl

rsa260LocalValidityDoesNotCreateWhole :
  RSA.LocalChunkValidityImpliesGlobalCarrier → ⊥
rsa260LocalValidityDoesNotCreateWhole =
  RSA.localValidityDoesNotCreateGlobalCarrier

------------------------------------------------------------------------
-- Canonical boundary reused directly.  This is the key extra firewall for the
-- package/reconstruction lanes: exact reconstruction is not historical custody.
------------------------------------------------------------------------

multipartBoundary : Multipart.MultipartReconstructionBoundary
multipartBoundary = Multipart.canonicalMultipartReconstructionBoundary

reconstructionCreatesHistoricalCustody : Bool
reconstructionCreatesHistoricalCustody =
  Multipart.reconstructionCreatesHistoricalCustody multipartBoundary

reconstructionCreatesHistoricalCustodyIsFalse :
  reconstructionCreatesHistoricalCustody ≡ false
reconstructionCreatesHistoricalCustodyIsFalse =
  Multipart.reconstructionCreatesHistoricalCustodyIsFalse multipartBoundary

------------------------------------------------------------------------
-- Status reading.
--
-- RSA has paid the *shape of the obligations* and the finite chunk arithmetic,
-- but the production bytes and same-object chunk manifest remain open.  The
-- generic CompleteMultipartReconstruction record therefore remains a target,
-- not an inhabited value supplied by this adapter.
------------------------------------------------------------------------

record RSA260MultipartSpineBoundary : Set where
  constructor rsa260-multipart-spine-boundary
  field
    canonicalMultipartDisciplineApplies : Bool
    canonicalMultipartDisciplineAppliesIsTrue :
      canonicalMultipartDisciplineApplies ≡ true
    requirementCrosswalkPaid : Bool
    requirementCrosswalkPaidIsTrue : requirementCrosswalkPaid ≡ true
    productionBytesPaid : Bool
    productionBytesPaidIsFalse : productionBytesPaid ≡ false
    completeSameObjectManifestPaid : Bool
    completeSameObjectManifestPaidIsFalse :
      completeSameObjectManifestPaid ≡ false
    historicalCustodyPaidByReconstruction : Bool
    historicalCustodyPaidByReconstructionIsFalse :
      historicalCustodyPaidByReconstruction ≡ false

canonicalRSA260MultipartSpineBoundary : RSA260MultipartSpineBoundary
canonicalRSA260MultipartSpineBoundary =
  rsa260-multipart-spine-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
