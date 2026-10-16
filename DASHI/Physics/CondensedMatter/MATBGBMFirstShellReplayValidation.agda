module DASHI.Physics.CondensedMatter.MATBGBMFirstShellReplayValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.CondensedMatter.MATBGBMFirstShellReplayReceiptExact as Replay

pythonAssertionsPassed : Replay.assertionsPassed Replay.canonicalFirstShellReplayReceipt ≡ true
pythonAssertionsPassed = refl

firstShellExecutionIsPaid : Replay.firstShellNumericalExecutionPaid Replay.canonicalFirstShellReplayBoundary ≡ true
firstShellExecutionIsPaid = refl

fullPlaneWaveConvergenceIsNotPaid : Replay.fullPlaneWaveConvergencePaid Replay.canonicalFirstShellReplayBoundary ≡ false
fullPlaneWaveConvergenceIsNotPaid = refl

qtmDataReplayIsNotPaid : Replay.qtmDataReplayPaid Replay.canonicalFirstShellReplayBoundary ≡ false
qtmDataReplayIsNotPaid = refl
