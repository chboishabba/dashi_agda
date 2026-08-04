module DASHI.Physics.Closure.NSTriadKNLuoFinitePrefixJensenExact where

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
-- Mathematical ingredients: finite Jensen/Cauchy--Schwarz and the elementary
-- dyadic count estimate q+1 <= 2^q for q>=0 in the repository's one-based
-- prefix convention.
--
-- PURPOSE
-- Derive the concrete source-shaped prefix estimate
--
--   (sum_{r=0}^q a_r)^2
--     <= 2^q sum_{r=0}^q a_r^2.
--
-- The list representing the complete prefix is constructed recursively;
-- agreement with the repository sumTo fold, the exact prefix cardinality,
-- and the dyadic cardinality domination are all proved.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality
  using (cong; subst; subst₂; trans)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Sum
import DASHI.Physics.Closure.NSTriadKNLuoFiniteJensenSquareExact as Jensen

two : ℚ
two = Int.+ 2 / 1

twoNonnegative : 0ℚ ≤ two
twoNonnegative = toWitness {a? = 0ℚ ≤? two} _

oneNonnegative : 0ℚ ≤ 1ℚ
oneNonnegative = toWitness {a? = 0ℚ ≤? 1ℚ} _

prefixValues : (Nat → ℚ) → Nat → List ℚ
prefixValues values zero = values zero ∷ []
prefixValues values (suc cutoff) =
  values (suc cutoff) ∷ prefixValues values cutoff

prefixSumAgreement :
  (values : Nat → ℚ) →
  (cutoff : Nat) →
  Jensen.sumValues (prefixValues values cutoff)
  ≡ Sum.sumTo values cutoff
prefixSumAgreement values zero = refl
prefixSumAgreement values (suc cutoff)
  rewrite prefixSumAgreement values cutoff = refl

prefixSquareSumAgreement :
  (values : Nat → ℚ) →
  (cutoff : Nat) →
  Jensen.sumSquares (prefixValues values cutoff)
  ≡ Sum.sumTo (λ index → L2.square (values index)) cutoff
prefixSquareSumAgreement values zero = refl
prefixSquareSumAgreement values (suc cutoff)
  rewrite prefixSquareSumAgreement values cutoff = refl

prefixCount : Nat → ℚ
prefixCount zero = 1ℚ
prefixCount (suc cutoff) = 1ℚ + prefixCount cutoff

prefixLengthAgreement :
  (values : Nat → ℚ) →
  (cutoff : Nat) →
  Jensen.rationalLength (prefixValues values cutoff)
  ≡ prefixCount cutoff
prefixLengthAgreement values zero = refl
prefixLengthAgreement values (suc cutoff)
  rewrite prefixLengthAgreement values cutoff = refl

powTwo : Nat → ℚ
powTwo zero = 1ℚ
powTwo (suc exponent) = two * powTwo exponent

powTwoNonnegative :
  (exponent : Nat) → 0ℚ ≤ powTwo exponent
powTwoNonnegative zero = oneNonnegative
powTwoNonnegative (suc exponent) =
  let
    instance
      twoIsNonnegative = nonNegative twoNonnegative
      previousIsNonnegative = nonNegative (powTwoNonnegative exponent)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg two (powTwo exponent)
  in
  ℚₚ.nonNegative⁻¹ (two * powTwo exponent)

oneBelowPowTwo :
  (exponent : Nat) → 1ℚ ≤ powTwo exponent
oneBelowPowTwo zero = ℚₚ.≤-refl
oneBelowPowTwo (suc exponent) =
  let
    first : 1ℚ ≤ 1ℚ + powTwo exponent
    first =
      subst
        (λ lower → lower ≤ 1ℚ + powTwo exponent)
        (ℚₚ.+-identityʳ 1ℚ)
        (ℚₚ.+-monoʳ-≤ 1ℚ (powTwoNonnegative exponent))

    second :
      1ℚ + powTwo exponent ≤ two * powTwo exponent
    second =
      let
        instance previousIsNonnegative =
          nonNegative (powTwoNonnegative exponent)
      in
      subst
        (λ right → 1ℚ + powTwo exponent ≤ right)
        (solve (powTwo exponent ∷ []))
        (ℚₚ.+-mono-≤
          (oneBelowPowTwo exponent)
          ℚₚ.≤-refl)
  in
  ℚₚ.≤-trans first second

prefixCountBelowPowTwo :
  (cutoff : Nat) → prefixCount cutoff ≤ powTwo cutoff
prefixCountBelowPowTwo zero = ℚₚ.≤-refl
prefixCountBelowPowTwo (suc cutoff) =
  let
    first :
      1ℚ + prefixCount cutoff
      ≤ 1ℚ + powTwo cutoff
    first =
      ℚₚ.+-mono-≤
        ℚₚ.≤-refl
        (prefixCountBelowPowTwo cutoff)

    second :
      1ℚ + powTwo cutoff
      ≤ two * powTwo cutoff
    second =
      let
        targetMeaning :
          two * powTwo cutoff
          ≡ powTwo cutoff + powTwo cutoff
        targetMeaning = solve (powTwo cutoff ∷ [])

        direct :
          1ℚ + powTwo cutoff
          ≤ powTwo cutoff + powTwo cutoff
        direct =
          ℚₚ.+-mono-≤
            (oneBelowPowTwo cutoff)
            ℚₚ.≤-refl
      in
      subst
        (λ right → 1ℚ + powTwo cutoff ≤ right)
        (symmetry targetMeaning)
        direct
  in
  ℚₚ.≤-trans first second
  where
  symmetry : ∀ {left right : ℚ} → left ≡ right → right ≡ left
  symmetry refl = refl

prefixSquareSumNonnegative :
  (values : Nat → ℚ) →
  (cutoff : Nat) →
  0ℚ ≤ Sum.sumTo (λ index → L2.square (values index)) cutoff
prefixSquareSumNonnegative values cutoff =
  Sum.sumToNonnegative
    (λ index → L2.square (values index))
    cutoff
    (λ index → L2.squareNonnegative (values index))

finitePrefixJensen :
  (values : Nat → ℚ) →
  (cutoff : Nat) →
  L2.square (Sum.sumTo values cutoff)
  ≤ prefixCount cutoff
      * Sum.sumTo (λ index → L2.square (values index)) cutoff
finitePrefixJensen values cutoff =
  let
    listBound = Jensen.finiteJensenSquare (prefixValues values cutoff)

    leftMeaning :
      L2.square (Jensen.sumValues (prefixValues values cutoff))
      ≡ L2.square (Sum.sumTo values cutoff)
    leftMeaning = cong L2.square (prefixSumAgreement values cutoff)

    rightMeaning :
      Jensen.sumSquares (prefixValues values cutoff)
        * Jensen.rationalLength (prefixValues values cutoff)
      ≡ prefixCount cutoff
        * Sum.sumTo (λ index → L2.square (values index)) cutoff
    rightMeaning
      rewrite prefixSquareSumAgreement values cutoff
            | prefixLengthAgreement values cutoff =
      solve
        ( prefixCount cutoff
        ∷ Sum.sumTo (λ index → L2.square (values index)) cutoff
        ∷ []
        )
  in
  subst₂ _≤_ leftMeaning rightMeaning listBound

finiteDyadicPrefixJensen :
  (values : Nat → ℚ) →
  (cutoff : Nat) →
  L2.square (Sum.sumTo values cutoff)
  ≤ powTwo cutoff
      * Sum.sumTo (λ index → L2.square (values index)) cutoff
finiteDyadicPrefixJensen values cutoff =
  ℚₚ.≤-trans
    (finitePrefixJensen values cutoff)
    (let instance squareSumIsNonnegative =
       nonNegative (prefixSquareSumNonnegative values cutoff)
     in
     ℚₚ.*-monoʳ-≤-nonNeg
       (Sum.sumTo (λ index → L2.square (values index)) cutoff)
       (prefixCountBelowPowTwo cutoff))

finitePrefixJensenClosed : Bool
finitePrefixJensenClosed = true

finiteDyadicPrefixJensenClosed : Bool
finiteDyadicPrefixJensenClosed = true

finitePrefixJensenClosedIsTrue :
  finitePrefixJensenClosed ≡ true
finitePrefixJensenClosedIsTrue = refl

finiteDyadicPrefixJensenClosedIsTrue :
  finiteDyadicPrefixJensenClosed ≡ true
finiteDyadicPrefixJensenClosedIsTrue = refl
