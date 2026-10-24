module DASHI.Physics.CondensedMatter.MATBGEntropyMaxwellReplayContractValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false; true)

import DASHI.Physics.CondensedMatter.MATBGEntropyMaxwellReplayContractExact as M

source-algorithm-paid : M.sourceAlgorithmExecutionPaid M.canonicalEntropyMaxwellReplayReceipt ≡ true
source-algorithm-paid = refl

measured-replay-still-open : M.measuredEntropyReplayPaid M.canonicalEntropyMaxwellReplayReceipt ≡ false
measured-replay-still-open = refl

xlsx-not-used : M.experimentalWorkbookBytesUsed M.canonicalEntropyMaxwellReplayReceipt ≡ false
xlsx-not-used = refl

synthetic-does-not-promote : M.syntheticFixtureDoesNotCreateExperimentalAuthority M.canonicalEntropyMaxwellReplayBoundary ≡ true
synthetic-does-not-promote = refl
