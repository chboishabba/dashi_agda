module DASHI.Physics.CondensedMatter.MATBGBMPlaneWaveReplayValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.CondensedMatter.MATBGBMPlaneWaveReplayReceiptExact as Replay

planeWaveExecutionPaid : Replay.reciprocalLatticeExecutionPaid Replay.canonicalPlaneWaveReplayBoundary ≡ true
planeWaveExecutionPaid = refl

shellConvergencePaid : Replay.shell3To4ConvergencePaid Replay.canonicalPlaneWaveReplayBoundary ≡ true
shellConvergencePaid = refl

magicAngleCrosscheckPaid : Replay.relaxedMagicAngleCrosscheckPaid Replay.canonicalPlaneWaveReplayBoundary ≡ true
magicAngleCrosscheckPaid = refl

xiaoAbsoluteCalibrationStillFalse : Replay.xiaoAbsoluteSampleCalibrationPaid Replay.canonicalPlaneWaveReplayBoundary ≡ false
xiaoAbsoluteCalibrationStillFalse = refl

qtmReplayStillFalse : Replay.qtmDataReplayPaid Replay.canonicalPlaneWaveReplayBoundary ≡ false
qtmReplayStillFalse = refl
