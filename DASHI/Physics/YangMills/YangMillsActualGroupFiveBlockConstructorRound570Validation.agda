{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsActualGroupFiveBlockConstructorRound570Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsActualGroupFiveBlockConstructorRound570Exact as R570
open import DASHI.Physics.YangMills.CompactLieProofLevel

constructorMachineChecked :
  R570.round570FiveBlockConstructorLevel ≡ machineChecked
constructorMachineChecked = refl

alignmentMachineChecked :
  R570.round570FiveBlockAlignmentLevel ≡ machineChecked
alignmentMachineChecked = refl
