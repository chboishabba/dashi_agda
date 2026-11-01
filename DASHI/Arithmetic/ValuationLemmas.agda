module DASHI.Arithmetic.ValuationLemmas where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; _∸_; z≤n)

open import MonsterOntos using (SSP)

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using
  ( Int
  ; alphaAt
  ; betaAt
  ; deltaAt
  )

open import DASHI.Arithmetic.NatBoolEquality using (natEq)
open import DASHI.Arithmetic.VpDepth using (minNat)
open import DASHI.Arithmetic.VpAddUnequal using (vp-add-min-unequal)

same-minus-zero : ∀ n → n ∸ n ≡ zero
same-minus-zero zero = refl
same-minus-zero (suc n) = same-minus-zero n

deltaNonnegative :
  ∀ p x y →
  zero ≤ deltaAt p x y
deltaNonnegative _ _ _ = z≤n

offWallZero :
  ∀ p x y →
  natEq (alphaAt p x y) (betaAt p x y) ≡ false →
  deltaAt p x y ≡ zero
offWallZero p x y wallFalse rewrite vp-add-min-unequal p x y wallFalse =
  same-minus-zero (minNat (alphaAt p x y) (betaAt p x y))
