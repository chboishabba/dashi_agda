module DASHI.Physics.CondensedMatter.MATBGTHFHubbardIAtomicReplayValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.CondensedMatter.MATBGTHFHubbardIAtomicReplayReceiptExact as Replay

atomic-reference-executed : Replay.atomicReferenceExecutionPaid Replay.canonicalTHFHubbardIAtomicReplayBoundary ≡ true
atomic-reference-executed = refl

self-consistency-still-open : Replay.selfConsistentCFHybridizationPaid Replay.canonicalTHFHubbardIAtomicReplayBoundary ≡ false
self-consistency-still-open = refl
