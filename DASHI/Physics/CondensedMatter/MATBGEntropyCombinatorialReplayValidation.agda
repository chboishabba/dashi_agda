module DASHI.Physics.CondensedMatter.MATBGEntropyCombinatorialReplayValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.CondensedMatter.MATBGEntropyCombinatorialReplayReceiptExact as Replay

logarithm-replay-paid : Replay.combinatorialLogarithmReplayPaid Replay.canonicalEntropyCombinatorialReplayBoundary ≡ true
logarithm-replay-paid = refl

measured-curve-replay-open : Replay.measuredEntropyCurveReplayPaid Replay.canonicalEntropyCombinatorialReplayBoundary ≡ false
measured-curve-replay-open = refl
