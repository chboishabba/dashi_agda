{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayRepresentedTerminalRound484Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsClayRepresentedTerminalRound484Exact as R484
open import DASHI.Physics.YangMills.CompactLieProofLevel

compilerMachineChecked :
  R484.round484RepresentedTerminalCompilerLevel ≡ machineChecked
compilerMachineChecked = refl

bareFunctionalTerminalPruned :
  R484.bareExpectationFunctionalTerminalRequired ≡ false
bareFunctionalTerminalPruned = refl

independentContinuumSchwingerPruned :
  R484.independentContinuumAndSchwingerChoicesRequired ≡ false
independentContinuumSchwingerPruned = refl
