module DASHI.Codec.DNAFirstFormalismRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (zero; suc)

open import DASHI.Algebra.Trit using (neg; zer; pos; inv)
open import DASHI.Codec.BalancedTritBitFibre
open import DASHI.Codec.DNAFirstFormalism

------------------------------------------------------------------------
-- Executable carrier/involution witnesses.

complement-A-roundtrip : complement (complement A) ≡ A
complement-A-roundtrip = refl

complement-C-roundtrip : complement (complement C) ≡ C
complement-C-roundtrip = refl

negative-fibre-roundtrip : decodeFibre (encodeFibre neg) ≡ neg
negative-fibre-roundtrip = refl

zero-fibre-roundtrip : decodeFibre (encodeFibre zer) ≡ zer
zero-fibre-roundtrip = refl

positive-fibre-roundtrip : decodeFibre (encodeFibre pos) ≡ pos
positive-fibre-roundtrip = refl

negative-support-bit : supportBit (encodeFibre neg) ≡ true
negative-support-bit = refl

zero-support-bit : supportBit (encodeFibre zer) ≡ false
zero-support-bit = refl

positive-support-bit : supportBit (encodeFibre pos) ≡ true
positive-support-bit = refl

mirror-lives-in-sign-fibre :
  encodeFibre (inv neg) ≡ invertFibre (encodeFibre neg)
mirror-lives-in-sign-fibre = refl

zero-is-fixed-by-mirror :
  encodeFibre (inv zer) ≡ invertFibre (encodeFibre zer)
zero-is-fixed-by-mirror = refl

------------------------------------------------------------------------
-- The word [negative, zero, positive] emits three support bits plus two
-- sign bits. This is the exact n + k law, not a two-bits-per-trit claim.

three-trit-cost :
  wordBitCost (neg ∷ zer ∷ pos ∷ []) ≡ suc (suc (suc (suc (suc zero))))
three-trit-cost = refl

three-trit-support-plus-sign :
  wordBitCost (neg ∷ zer ∷ pos ∷ []) ≡
  length (neg ∷ zer ∷ pos ∷ []) +
  nonZeroCount (neg ∷ zer ∷ pos ∷ [])
three-trit-support-plus-sign = wordBitCost-support-plus-sign _

------------------------------------------------------------------------
-- Empty DNA traces are generable for every constraint machine. Non-empty
-- traces require an admissibility witness at every emitted base.

empty-is-generable :
  ∀ M → Generable M []
empty-is-generable M = emptyTrace
