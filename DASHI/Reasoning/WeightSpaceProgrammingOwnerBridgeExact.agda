module DASHI.Reasoning.WeightSpaceProgrammingOwnerBridgeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Reasoning.WeightSpaceProgrammingInterventionExact as WSP
import DASHI.Reasoning.StructuralMetaphorTaskCompressionExact as Compression
import DASHI.Reasoning.RelationRepresentationRealizationExact as Realization

------------------------------------------------------------------------
-- Existing-owner reuse only.  This bridge intentionally is NOT marked
-- --safe, because the historical owner graph is not wholly safe-qualified.
-- The standalone constructive WSP intervention owner remains --safe.
------------------------------------------------------------------------

reportedIntactChannelCollision :
  Compression.CompressionFailureWitness
    WSP.stableChannel WSP.taskBehavior
reportedIntactChannelCollision =
  Compression.compressionFailureWitness
    WSP.loopingWorld WSP.productiveWorld refl (λ ())

noAutomaticBenchmarkFromIntactChannel :
  Realization.RepresentationRealizationWitness
    WSP.stableChannel WSP.taskBehavior → ⊥
noAutomaticBenchmarkFromIntactChannel =
  Realization.representationCollisionBlocksRealization
    reportedIntactChannelCollision
