module DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedIncrementFubiniExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions
-- of Euler's Equation".
-- Communications in Mathematical Physics 165 (1994), 207--209.
-- DOI: 10.1007/BF02099744.
--
-- PURPOSE
-- Prove the finite Fubini step required when the weighted displacement sum
-- and resonant-pair convolution are both finite.  For arbitrary finite lists,
--
--   sum_pair sum_sample F(pair,sample)
--     = sum_sample sum_pair F(pair,sample).
--
-- The proof derives zero-sum and pointwise-add distribution lemmas and then
-- performs induction on the outer list.  No interchange equality is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; sym)
open Eq.≡-Reasoning

sumList :
  ∀ {A : Set} → List A → (A → ℚ) → ℚ
sumList [] value = 0ℚ
sumList (x ∷ xs) value = value x + sumList xs value

sumListZero :
  ∀ {A : Set} (xs : List A) →
  sumList xs (λ _ → 0ℚ) ≡ 0ℚ
sumListZero [] = refl
sumListZero (x ∷ xs)
  rewrite sumListZero xs = solve []

sumListPointwiseAdd :
  ∀ {A : Set}
    (xs : List A)
    (left right : A → ℚ) →
  sumList xs (λ x → left x + right x)
  ≡ sumList xs left + sumList xs right
sumListPointwiseAdd [] left right = solve []
sumListPointwiseAdd (x ∷ xs) left right
  rewrite sumListPointwiseAdd xs left right =
  solve
    ( left x
    ∷ right x
    ∷ sumList xs left
    ∷ sumList xs right
    ∷ []
    )

finiteFubini :
  ∀ {A B : Set}
    (as : List A)
    (bs : List B)
    (value : A → B → ℚ) →
  sumList as (λ a → sumList bs (value a))
  ≡ sumList bs (λ b → sumList as (λ a → value a b))
finiteFubini [] bs value =
  sym (sumListZero bs)
finiteFubini (a ∷ as) bs value =
  begin
    sumList (a ∷ as) (λ outer → sumList bs (value outer))
  ≡⟨ refl ⟩
    sumList bs (value a)
      + sumList as (λ outer → sumList bs (value outer))
  ≡⟨ cong
       (sumList bs (value a) +_)
       (finiteFubini as bs value) ⟩
    sumList bs (value a)
      + sumList bs (λ b → sumList as (λ outer → value outer b))
  ≡⟨ sym
       (sumListPointwiseAdd
         bs
         (value a)
         (λ b → sumList as (λ outer → value outer b))) ⟩
    sumList bs
      (λ b → value a b + sumList as (λ outer → value outer b))
  ≡⟨ refl ⟩
    sumList bs (λ b → sumList (a ∷ as) (λ outer → value outer b))
  ∎

finitePairSampleInterchange :
  ∀ {Pair Sample : Set}
    (pairs : List Pair)
    (samples : List Sample)
    (weightedIncrementTerm : Pair → Sample → ℚ) →
  sumList pairs
    (λ pair → sumList samples (weightedIncrementTerm pair))
  ≡ sumList samples
      (λ sample →
        sumList pairs (λ pair → weightedIncrementTerm pair sample))
finitePairSampleInterchange = finiteFubini

finitePairSampleFubiniClosed : Bool
finitePairSampleFubiniClosed = true

finitePairSampleFubiniClosedIsTrue :
  finitePairSampleFubiniClosed ≡ true
finitePairSampleFubiniClosedIsTrue = refl
