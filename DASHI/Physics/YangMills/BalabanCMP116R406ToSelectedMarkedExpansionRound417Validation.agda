{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R406ToSelectedMarkedExpansionRound417Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCMP116R406ToSelectedMarkedExpansionRound417Exact as R417
open import DASHI.Physics.YangMills.CompactLieProofLevel

r406ReuseCompilerMachineChecked :
  R417.round417R406ExpansionReuseCompilerLevel ≡ machineChecked
r406ReuseCompilerMachineChecked = refl

duplicateLiteralExpansionFieldsPruned :
  R417.round417DuplicateLiteralExpansionFieldsRequired ≡ false
duplicateLiteralExpansionFieldsPruned = refl
