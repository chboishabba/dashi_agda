module DASHI.ComputerScience.RSA260MultipartReconstructionSpineRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260MultipartReconstructionSpineExact as Adapter
import DASHI.ComputerScience.RSA260369DNA27CodecNDimTetrationCrossPollinationExact as RSA

localDigestRequirementRetained :
  RSA.localChunkDigestRequired RSA.currentArtifactManifestBoundary ≡ true
localDigestRequirementRetained = Adapter.rsa260LocalChunkDigestRequired

chunkPositionRequirementRetained :
  RSA.chunkPositionRequired RSA.currentArtifactManifestBoundary ≡ true
chunkPositionRequirementRetained = Adapter.rsa260ChunkPositionRequired

seamCompatibilityRequirementRetained :
  RSA.seamBoundaryCompatibilityRequired RSA.currentArtifactManifestBoundary ≡ true
seamCompatibilityRequirementRetained = Adapter.rsa260SeamCompatibilityRequired

globalReconstructionRequirementRetained :
  RSA.globalReconstructionReceiptRequired RSA.currentArtifactManifestBoundary ≡ true
globalReconstructionRequirementRetained = Adapter.rsa260GlobalReconstructionReceiptRequired

globalSameObjectRequirementRetained :
  RSA.globalSameObjectDigestRequired RSA.currentArtifactManifestBoundary ≡ true
globalSameObjectRequirementRetained = Adapter.rsa260GlobalSameObjectDigestRequired

missingChunkCannotBeIgnored :
  RSA.conclusionPaymentMayIgnoreMissingChunk RSA.currentArtifactManifestBoundary ≡ false
missingChunkCannotBeIgnored = Adapter.rsa260MissingChunkCannotPayWhole

completedManifestStillUnpaid :
  RSA.sameObjectChunkManifestPaid RSA.currentRSA260369DNA27RoadmapBoundary ≡ false
completedManifestStillUnpaid = Adapter.rsa260CompleteMultipartReconstructionStillUnpaid

localValidityStillDoesNotCreateGlobalCarrier :
  RSA.LocalChunkValidityImpliesGlobalCarrier → ⊥
localValidityStillDoesNotCreateGlobalCarrier =
  Adapter.rsa260LocalValidityDoesNotCreateWhole

reconstructionDoesNotCreateHistoricalCustody :
  Adapter.reconstructionCreatesHistoricalCustody ≡ false
reconstructionDoesNotCreateHistoricalCustody = refl
