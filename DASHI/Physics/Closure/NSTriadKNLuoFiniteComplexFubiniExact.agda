module DASHI.Physics.Closure.NSTriadKNLuoFiniteComplexFubiniExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Guido Fubini; Agda standard-library contributors;
-- DASHI repository contributors.
-- Result: finite Fubini/interchange theorem for complex-valued sums.
-- DOI: not applicable to this finite repository-specialised theorem.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Prove the finite sum/interchange theorem on the literal complex Fourier
-- carrier.  For arbitrary finite pair and displacement lists,
--
--   sum_pair sum_sample F(pair,sample)
--     = sum_sample sum_pair F(pair,sample).
--
-- Zero sums and pointwise-add distribution are proved first; the Fubini
-- identity then follows by induction on the pair list.  No interchange law is
-- accepted as an input.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; sym)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring

complexSum :
  ∀ {r} {F : C3.RealField r} {A : Set} →
  List A → (A → C3.Complex F) → C3.Complex F
complexSum {F = F} [] value = C3.complexZero F
complexSum (x ∷ xs) value =
  C3.complexAdd (value x) (complexSum xs value)

complexSumZero :
  ∀ {r} {F : C3.RealField r} {A : Set}
    (xs : List A) →
  complexSum {F = F} xs (λ _ → C3.complexZero F)
  ≡ C3.complexZero F
complexSumZero {F = F} [] = refl
complexSumZero {F = F} (x ∷ xs)
  rewrite complexSumZero {F = F} xs =
  Algebra.complexAddZeroLeft (C3.complexZero F)

complexSumPointwiseAdd :
  ∀ {r} {F : C3.RealField r} {A : Set}
    (xs : List A)
    (left right : A → C3.Complex F) →
  complexSum xs
    (λ x → C3.complexAdd (left x) (right x))
  ≡ C3.complexAdd
      (complexSum xs left)
      (complexSum xs right)
complexSumPointwiseAdd {F = F} [] left right =
  sym (Algebra.complexAddZeroLeft (C3.complexZero F))
complexSumPointwiseAdd {F = F} (x ∷ xs) left right
  rewrite complexSumPointwiseAdd xs left right =
  R.solve 4
    (λ leftHead rightHead leftTail rightTail →
      ((leftHead R.⊕ rightHead) R.⊕ (leftTail R.⊕ rightTail))
      R.⊜
      ((leftHead R.⊕ leftTail) R.⊕ (rightHead R.⊕ rightTail)))
    refl
    (left x)
    (right x)
    (complexSum xs left)
    (complexSum xs right)
  where module R = Ring.Solver F

finiteComplexFubini :
  ∀ {r} {F : C3.RealField r} {A B : Set}
    (as : List A)
    (bs : List B)
    (value : A → B → C3.Complex F) →
  complexSum as (λ a → complexSum bs (value a))
  ≡ complexSum bs (λ b → complexSum as (λ a → value a b))
finiteComplexFubini {F = F} [] bs value =
  sym (complexSumZero {F = F} bs)
finiteComplexFubini {F = F} (a ∷ as) bs value =
  begin
    complexSum (a ∷ as) (λ outer → complexSum bs (value outer))
  ≡⟨ refl ⟩
    C3.complexAdd
      (complexSum bs (value a))
      (complexSum as (λ outer → complexSum bs (value outer)))
  ≡⟨ cong
       (λ tail → C3.complexAdd (complexSum bs (value a)) tail)
       (finiteComplexFubini as bs value) ⟩
    C3.complexAdd
      (complexSum bs (value a))
      (complexSum bs (λ b → complexSum as (λ outer → value outer b)))
  ≡⟨ sym
       (complexSumPointwiseAdd
         bs
         (value a)
         (λ b → complexSum as (λ outer → value outer b))) ⟩
    complexSum bs
      (λ b →
        C3.complexAdd
          (value a b)
          (complexSum as (λ outer → value outer b)))
  ≡⟨ refl ⟩
    complexSum bs
      (λ b → complexSum (a ∷ as) (λ outer → value outer b))
  ∎

finiteComplexPairSampleInterchange :
  ∀ {r} {F : C3.RealField r} {Pair Sample : Set}
    (pairs : List Pair)
    (samples : List Sample)
    (weightedIncrementTerm : Pair → Sample → C3.Complex F) →
  complexSum pairs
    (λ pair → complexSum samples (weightedIncrementTerm pair))
  ≡ complexSum samples
      (λ sample →
        complexSum pairs
          (λ pair → weightedIncrementTerm pair sample))
finiteComplexPairSampleInterchange = finiteComplexFubini

finiteComplexFubiniClosed : Bool
finiteComplexFubiniClosed = true

finiteComplexPairSampleInterchangeClosed : Bool
finiteComplexPairSampleInterchangeClosed = true

finiteComplexFubiniClosedIsTrue :
  finiteComplexFubiniClosed ≡ true
finiteComplexFubiniClosedIsTrue = refl

finiteComplexPairSampleInterchangeClosedIsTrue :
  finiteComplexPairSampleInterchangeClosed ≡ true
finiteComplexPairSampleInterchangeClosedIsTrue = refl
