module DASHI.Physics.Probes.YMPromotionProbe where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.YMFinalStateReceipt as Root

record YMPromotionContract : Set where
  field
    ymL3TightnessConstructed :
      Root.ymL3TightnessConstructed Root.canonicalYMFinalStateReceipt ≡ true

    fullTightnessConstructed :
      Root.fullTightnessConstructed Root.canonicalYMFinalStateReceipt ≡ true

    continuumYangMillsConstructed :
      Root.continuumYangMillsConstructed Root.canonicalYMFinalStateReceipt ≡ true

    gaugeSectorOSContinuumConstructed :
      Root.gaugeSectorOSContinuumConstructed Root.canonicalYMFinalStateReceipt ≡ true

    uniformMassGapConstructed :
      Root.uniformMassGapConstructed Root.canonicalYMFinalStateReceipt ≡ true

    continuumUniquenessConstructed :
      Root.continuumUniquenessConstructed Root.canonicalYMFinalStateReceipt ≡ true

    clayYangMillsPromoted :
      Root.clayYangMillsPromoted Root.canonicalYMFinalStateReceipt ≡ true

    terminalClayClaimPromoted :
      Root.terminalClayClaimPromoted Root.canonicalYMFinalStateReceipt ≡ true

ymPromotionProbe : YMPromotionContract
ymPromotionProbe =
  record
    { ymL3TightnessConstructed = refl
    ; fullTightnessConstructed = refl
    ; continuumYangMillsConstructed = refl
    ; gaugeSectorOSContinuumConstructed = refl
    ; uniformMassGapConstructed = refl
    ; continuumUniquenessConstructed = refl
    ; clayYangMillsPromoted = refl
    ; terminalClayClaimPromoted = refl
    }
