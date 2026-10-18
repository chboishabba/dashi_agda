{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsRationalAbsoluteCovarianceExtensionRound575Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsRationalAbsoluteCovarianceExtensionRound575Exact as R575
open import DASHI.Physics.YangMills.CompactLieProofLevel

extensionCompilerMachineChecked :
  R575.round575RationalCovarianceExtensionCompilerLevel ≡ machineChecked
extensionCompilerMachineChecked = refl

magnitudeCalibrationMachineChecked :
  R575.round575MagnitudeCalibrationCompilerLevel ≡ machineChecked
magnitudeCalibrationMachineChecked = refl

continuityIsStandardImported :
  R575.round575RationalCovarianceContinuityLawsLevel ≡ standardImported
continuityIsStandardImported = refl
