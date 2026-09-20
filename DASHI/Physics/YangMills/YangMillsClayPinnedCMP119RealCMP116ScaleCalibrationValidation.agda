{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ScaleCalibrationValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119RealCMP116ScaleCalibrationExact

physicalScaleTransportIsMachineChecked :
  literalRealCMP116PhysicalScaleTransportLevel ≡ machineChecked
physicalScaleTransportIsMachineChecked = refl

envelopeToPhysicalUpperIsMachineChecked :
  literalRealCMP116EnvelopeToPhysicalUpperCompilerLevel ≡ machineChecked
envelopeToPhysicalUpperIsMachineChecked = refl

remainingSourcePaymentIsConditional :
  literalCMP116SelectedEnvelopeExponentialIdentificationLevel ≡ conditional
remainingSourcePaymentIsConditional = refl
