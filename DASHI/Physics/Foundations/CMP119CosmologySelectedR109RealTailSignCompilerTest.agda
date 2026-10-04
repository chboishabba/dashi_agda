{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologySelectedR109RealTailSignCompilerTest where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologySelectedR109RealTailSignCompilerExact as Cut

selectedRealTailSignCompilerPresent : Bool
selectedRealTailSignCompilerPresent = Cut.realCompletionTailSignCompilerOwned

selectedRealTailSignCompilerPresent-is-true :
  selectedRealTailSignCompilerPresent ≡ true
selectedRealTailSignCompilerPresent-is-true = refl
