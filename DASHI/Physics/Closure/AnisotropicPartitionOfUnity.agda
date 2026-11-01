module DASHI.Physics.Closure.AnisotropicPartitionOfUnity where

open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- The partition-of-unity identity for spatial-only polymer steps:
-- A polymer that is spatially confined (inSpatialOnly)
-- cannot simultaneously be in both temporal faces of any block.
-- This is the algebraic statement that L³ entropy counting is valid:
-- temporal polymers do not re-enter the spatial RG entropy sum.

record AnisotropicPartitionOfUnity
    (Carrier  : Set)
    (Polymer  : Set)
    (Block    : Set)
    (inBlock  : Polymer → Block → Set)
    (inSpatialOnly  : Polymer → Set)
    (inTopTemporal  : Polymer → Block → Set)
    (inBotTemporal  : Polymer → Block → Set) : Set where
  field
    -- Core identity: spatial-only polymers are excluded from both
    -- temporal faces simultaneously. Proved from the inBlock
    -- predicate structure.
    spatialExcludesDualTemporal :
        ∀ p b → inSpatialOnly p
              → inTopTemporal p b
              → inBotTemporal p b
              → ⊥

    -- The spatial face covers all non-temporal polymer support.
    -- This gives the partition completeness direction.
    partitionCompleteness :
        ∀ p b → inBlock p b
              → inSpatialOnly p
                ⊎ inTopTemporal p b
                ⊎ inBotTemporal p b
