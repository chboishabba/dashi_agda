module DASHI.Foundations.StageTetralemmaArrestBridge where

open import DASHI.Core.Prelude

import LogicTlurey as Tlurey
import DASHI.Foundations.StageValuationBundleAtlas as Stage

------------------------------------------------------------------------
-- The existing four-stage dialectic sends overflow back to the seed tone.
-- The guarded Stage-4 -> Stage-1 edge records the arrested case where no
-- additional valuation, memory or learning witness carries new information
-- across that quotient seam.
------------------------------------------------------------------------

overflowToneCollapsesToSeedTone :
  Tlurey.stageTone Tlurey.overflow
  ≡ Tlurey.stageTone Tlurey.seed
overflowToneCollapsesToSeedTone = refl

fourStepsReturnToSeed :
  Tlurey.spin 4 Tlurey.next Tlurey.seed
  ≡ Tlurey.seed
fourStepsReturnToSeed = Tlurey.next⁴ Tlurey.seed

record TetralemmaArrestReceipt : Set where
  field
    toneCollapse :
      Tlurey.stageTone Tlurey.overflow
      ≡ Tlurey.stageTone Tlurey.seed
    cycleReturns :
      Tlurey.spin 4 Tlurey.next Tlurey.seed
      ≡ Tlurey.seed
    guardedArrestTransition :
      Stage.ValuationGuardedTransition
    insufficientDepthRecorded : Bool
    counterpositionIntegratedClaimed : Bool
    synthesisPromoted : Bool

canonicalTetralemmaArrestReceipt : TetralemmaArrestReceipt
canonicalTetralemmaArrestReceipt = record
  { toneCollapse = overflowToneCollapsesToSeedTone
  ; cycleReturns = fourStepsReturnToSeed
  ; guardedArrestTransition = Stage.canonicalArrestedTetralemma
  ; insufficientDepthRecorded = true
  ; counterpositionIntegratedClaimed = false
  ; synthesisPromoted = false
  }
