{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5MarkedPreferredExpectationRound445Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanClayT5MarkedPreferredExpectationRound445Exact as R445
open import DASHI.Physics.YangMills.CompactLieProofLevel

markedPreferredCompilerMachineChecked :
  R445.round445MarkedPreferredExpectationCompilerLevel ≡ machineChecked
markedPreferredCompilerMachineChecked = refl

independentMomentProducerPruned :
  R445.round445IndependentMomentProducerRequired ≡ false
independentMomentProducerPruned = refl
