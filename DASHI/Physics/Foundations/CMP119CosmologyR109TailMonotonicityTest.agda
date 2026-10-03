{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR109TailMonotonicityTest where

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base as Nat using (_≤_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

import DASHI.Physics.Foundations.CMP119CosmologyR109TailMonotonicityExact as TailMono
import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109

r109TailAntitoneRegression :
  (source : R109.SourceNativeStressScaleCauchy) →
  ∀ {near far : Nat} →
  near Nat.≤ far →
  Tail.r109RemainingTail source far ≤ Tail.r109RemainingTail source near
r109TailAntitoneRegression = TailMono.r109RemainingTailAntitone
