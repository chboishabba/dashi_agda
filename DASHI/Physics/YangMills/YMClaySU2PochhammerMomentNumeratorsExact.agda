{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClaySU2PochhammerMomentNumeratorsExact where

-- Source-first all-degree EXACT rational S3 monomial moment algorithm.
-- Computes numerator/denominator as natural numbers and independently
-- signals exactly zero odd moments. No analysis, legacy real, pi,
-- trigonometry, postulates or conditional measure fields are introduced.
--
-- H(prod q_i^(2a_i)) =
-- [prod_i (2a_i-1)!!]/[2^k (k+1)!], k=sum_i a_i.
-- Because (1/2)_a = (2a-1)!!/2^a and (2)_k=(k+1)!.
--
-- This is the finite polynomial evaluator, NOT an inhabited continuous
-- Haar functional or the proof of positivity/all-degree product cubature.
-- Attribution: Pizzetti/Folland exact sphere moments; original DASHI
-- rational SU2 and Bishop real theorem owners; Wilson/Balaban.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Maybe using (Maybe; nothing; just)
open import Agda.Builtin.Equality using (_≡_; refl)

record Exponents : Set where
  constructor powers
  field
    e0 e1 e2 e3 : Nat
open Exponents public

record Ratio : Set where
  constructor ratio
  field
    numerator denominator : Nat
open Ratio public

evenHalf : Nat → Maybe Nat
evenHalf zero = just zero
evenHalf (suc zero) = nothing
evenHalf (suc (suc n)) with evenHalf n
... | nothing = nothing
... | just a = just (suc a)

oddDoubleFactorial : Nat → Nat
oddDoubleFactorial zero = suc zero
oddDoubleFactorial (suc a) =
  suc (a + a) * oddDoubleFactorial a

factorial : Nat → Nat
factorial zero = suc zero
factorial (suc a) = suc a * factorial a

powerTwo : Nat → Nat
powerTwo zero = suc zero
powerTwo (suc a) = suc (suc zero) * powerTwo a

exactMoment : Exponents → Maybe Ratio
exactMoment (powers e0 e1 e2 e3)
  with evenHalf e0 | evenHalf e1 | evenHalf e2 | evenHalf e3
... | just a | just b | just c | just d =
  let k = a + b + c + d in
  just (ratio
    (oddDoubleFactorial a * oddDoubleFactorial b *
     oddDoubleFactorial c * oddDoubleFactorial d)
    (powerTwo k * factorial (suc k)))
... | _ | _ | _ | _ = nothing

momentOne :
  exactMoment (powers 0 0 0 0) ≡ just (ratio 1 1)
momentOne = refl

momentQ0 :
  exactMoment (powers 1 0 0 0) ≡ nothing
momentQ0 = refl

momentQ0Squared :
  exactMoment (powers 2 0 0 0) ≡ just (ratio 1 4)
momentQ0Squared = refl

momentQ0Fourth :
  exactMoment (powers 4 0 0 0) ≡ just (ratio 3 24)
momentQ0Fourth = refl

momentQ0SqQ1Sq :
  exactMoment (powers 2 2 0 0) ≡ just (ratio 1 24)
momentQ0SqQ1Sq = refl
