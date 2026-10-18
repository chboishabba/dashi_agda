{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsLiteralCMP119QuantitativeMomentsRound559Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsLiteralCMP119QuantitativeMomentsRound559Exact as R559
open import DASHI.Physics.YangMills.CompactLieProofLevel

literalMomentTransportMachineChecked :
  R559.round559LiteralCMP119MomentTransportLevel ≡ machineChecked
literalMomentTransportMachineChecked = refl

sameFiniteExpectationWeldPruned :
  R559.round559SameFiniteExpectationAttachmentRequired ≡ false
sameFiniteExpectationWeldPruned = refl
