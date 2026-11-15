{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativePositiveThresholdNonzeroExact where

------------------------------------------------------------------------
-- P0-E original strictly-positive N21 threshold: actual bit-native
-- predecessor + nonzero test. The original wire rejects threshold 0.
-- These lemmas never inspect a unary number at parser runtime.
--
-- This owner proves ALL-WORD numerical meaning of the actual anyOne
-- Boolean zero test, and every successful positive-gamma native
-- threshold carries a strictly positive numerical witness.
--
-- Still missing: full original graph-word all-field/cursor weld and
-- the threshold atLeast-vs-original signed raw-score assembly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Product using (Σ; _,_)
open import Data.List.Base using (reverse)
open import Data.Nat.Tactic.RingSolver using (solve)
open import Data.Maybe.Base using (just; nothing)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePositiveThresholdExact as Positive
import DASHI.Mathematics.Complexity.Karp21GammaBinaryNativePayloadExact as Gamma

-- Rejected zero bitstrings may contain arbitrarily many bits.
anyOneFalseMeansZero :
  (bits : Word.BitWord) →
  Positive.anyOne bits ≡ false →
  Value.valueLE bits ≡ zero
anyOneFalseMeansZero [] accepted = refl
anyOneFalseMeansZero (false ∷ rest) accepted
  rewrite anyOneFalseMeansZero rest accepted = refl
anyOneFalseMeansZero (true ∷ rest) ()

-- Every positive binary numeral has an explicitly exhibited
-- successor Nat value, including words containing redundant zeros.
anyOneTrueMeansPositive :
  (bits : Word.BitWord) →
  Positive.anyOne bits ≡ true →
  Σ Nat (λ n → Value.valueLE bits ≡ suc n)
anyOneTrueMeansPositive [] ()
anyOneTrueMeansPositive (true ∷ rest) observed =
  (Value.two * Value.valueLE rest) , refl
anyOneTrueMeansPositive (false ∷ rest) observed
  with anyOneTrueMeansPositive rest observed
... | k , equality rewrite equality =
  (suc (Value.two * k)) , solve (k ∷ [])

-- The ACTUAL gamma-prefix scan and binary predecessor reject zero
-- and return only positive threshold values; no premise about the
-- result's magnitude is supplied by the caller.
readPositiveGammaLEAlwaysPositive :
  (word threshold suffix : Word.BitWord) →
  Positive.readPositiveGammaLE word ≡
    just (threshold , suffix) →
  Σ Nat (λ n → Value.valueLE threshold ≡ suc n)
readPositiveGammaLEAlwaysPositive word threshold suffix accepted
  with Gamma.readGammaBinary word
... | nothing with accepted
... | ()
... | just (successor , after)
  with Positive.predecessorLE (reverse successor)
... | numeral
  with Positive.anyOne numeral in nonzero
... | false with accepted
... | ()
... | true with accepted
... | refl = anyOneTrueMeansPositive numeral nonzero
