module DASHI.Physics.CondensedMatter.MATBGQTMElectrostaticsReplayValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.CondensedMatter.MATBGQTMElectrostaticsReplayReceiptExact as Replay

capacitor-reference-executed : Replay.zeroChemicalPotentialCapacitorReferencePaid Replay.canonicalQTMElectrostaticsReplayBoundary ≡ true
capacitor-reference-executed = refl

measured-skew-map-open : Replay.measuredSkewMapReplayPaid Replay.canonicalQTMElectrostaticsReplayBoundary ≡ false
measured-skew-map-open = refl
