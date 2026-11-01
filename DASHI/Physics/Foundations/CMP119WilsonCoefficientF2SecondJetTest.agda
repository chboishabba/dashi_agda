{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119WilsonCoefficientF2SecondJetTest where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119WilsonCoefficientF2SecondJetExact as F

finiteWilsonF2Closed : F.finiteWilsonInsertionHasExactDiscreteF2SecondJet ≡ true
finiteWilsonF2Closed = refl

continuumOnlyRemains : F.remainingF2DebtIsRenormalizedCompletionNotFiniteIdentification ≡ true
continuumOnlyRemains = refl
