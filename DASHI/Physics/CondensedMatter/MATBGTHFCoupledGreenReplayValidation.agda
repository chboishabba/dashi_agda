module DASHI.Physics.CondensedMatter.MATBGTHFCoupledGreenReplayValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.CondensedMatter.MATBGTHFCoupledGreenReplayReceiptExact as Replay

coupled-block-executed : Replay.coupledGreenBlockExecutionPaid Replay.canonicalTHFCoupledGreenReplayBoundary ≡ true
coupled-block-executed = refl

self-consistency-still-open : Replay.selfConsistentDensitySolvePaid Replay.canonicalTHFCoupledGreenReplayBoundary ≡ false
self-consistency-still-open = refl
