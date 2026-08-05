module DASHI.Physics.Closure.NSTriadKNLuoFiniteExponentialPolynomialAbsorptionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Darko Mitrović.
-- Title: "A High-Frequency Tail Condition and a Diagnostic Iteration for
-- the Navier--Stokes Equations".
-- arXiv:2411.02568.
-- DOI: none assigned in the cited preprint version.
--
-- Mathematical ingredient: elementary dyadic domination of polynomial shell
-- multiplicity by a weaker geometric factor.
--
-- PURPOSE
-- Prove a concrete exponential-to-polynomial absorption rather than store it
-- as an eventual-tail field.  Since n+1 <= 2^n in the repository's one-based
-- prefix convention,
--
--   (n+1) (1/4)^n <= (1/2)^n.
--
-- Squaring the same estimate gives
--
--   (n+1)^2 (1/16)^n <= (1/4)^n.
--
-- These exact rational bounds let a damped far-history term pay finite shell
-- multiplicity.  They are a dyadic model of exponential absorption, not an
-- identification with the continuum exponential function.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoFinitePrefixJensenExact as Prefix
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

half sixteenth : ℚ
half = Int.+ 1 / 2
sixteenth = Int.+ 1 / 16

powerProduct :
  (left right : ℚ) →
  (exponent : Nat) →
  Geo.pow left exponent * Geo.pow right exponent
  ≡ Geo.pow (left * right) exponent
powerProduct left right zero = refl
powerProduct left right (suc exponent)
  rewrite powerProduct left right exponent =
  solve
    ( left
    ∷ right
    ∷ Geo.pow (left * right) exponent
    ∷ []
    )

twoQuarterPowerIsHalfPower :
  (exponent : Nat) →
  Prefix.powTwo exponent * Geo.pow Geo.quarter exponent
  ≡ Geo.pow half exponent
twoQuarterPowerIsHalfPower exponent =
  powerProduct Prefix.two Geo.quarter exponent

linearMultiplicityAbsorbed :
  (exponent : Nat) →
  Prefix.prefixCount exponent * Geo.pow Geo.quarter exponent
  ≤ Geo.pow half exponent
linearMultiplicityAbsorbed exponent =
  let
    quarterPowerNonnegative :
      0ℚ ≤ Geo.pow Geo.quarter exponent
    quarterPowerNonnegative =
      Geo.powNonnegative
        Geo.quarter exponent Geo.quarterNonnegative

    scaled :
      Prefix.prefixCount exponent * Geo.pow Geo.quarter exponent
      ≤ Prefix.powTwo exponent * Geo.pow Geo.quarter exponent
    scaled =
      let
        instance
          quarterPowerIsNonnegative =
            nonNegative quarterPowerNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (Geo.pow Geo.quarter exponent)
        (Prefix.prefixCountBelowPowTwo exponent)
  in
  subst
    (λ upper →
      Prefix.prefixCount exponent * Geo.pow Geo.quarter exponent
      ≤ upper)
    (twoQuarterPowerIsHalfPower exponent)
    scaled

squareLinearMultiplicityAbsorbed :
  (exponent : Nat) →
  L2.square (Prefix.prefixCount exponent)
    * Geo.pow sixteenth exponent
  ≤ Geo.pow Geo.quarter exponent
squareLinearMultiplicityAbsorbed exponent =
  let
    first = linearMultiplicityAbsorbed exponent

    squared :
      L2.square
        (Prefix.prefixCount exponent * Geo.pow Geo.quarter exponent)
      ≤ L2.square (Geo.pow half exponent)
    squared =
      let
        leftNonnegative :
          0ℚ ≤ Prefix.prefixCount exponent
              * Geo.pow Geo.quarter exponent
        leftNonnegative =
          let
            prefixNonnegative : 0ℚ ≤ Prefix.prefixCount exponent
            prefixNonnegative =
              Prefix.prefixSquareSumNonnegative
                (λ index → Int.+ 1 / 1)
                exponent

            quarterNonnegative =
              Geo.powNonnegative
                Geo.quarter exponent Geo.quarterNonnegative

            instance
              prefixIsNonnegative = nonNegative prefixNonnegative
              quarterIsNonnegative = nonNegative quarterNonnegative
              productIsNonnegative =
                ℚₚ.nonNeg*nonNeg⇒nonNeg
                  (Prefix.prefixCount exponent)
                  (Geo.pow Geo.quarter exponent)
          in
          ℚₚ.nonNegative⁻¹
            (Prefix.prefixCount exponent * Geo.pow Geo.quarter exponent)
      in
      squareMonotone leftNonnegative first

    leftMeaning :
      L2.square
        (Prefix.prefixCount exponent * Geo.pow Geo.quarter exponent)
      ≡ L2.square (Prefix.prefixCount exponent)
          * Geo.pow sixteenth exponent
    leftMeaning =
      beginLeft exponent

    rightMeaning :
      L2.square (Geo.pow half exponent)
      ≡ Geo.pow Geo.quarter exponent
    rightMeaning =
      powerProduct half half exponent
  in
  subst₂ _≤_ leftMeaning rightMeaning squared
  where
  squareMonotone :
    ∀ {left right : ℚ} →
    0ℚ ≤ left → left ≤ right →
    L2.square left ≤ L2.square right
  squareMonotone {left} {right} leftNonnegative leftBelowRight =
    let
      rightNonnegative = ℚₚ.≤-trans leftNonnegative leftBelowRight
      first =
        let instance leftIsNonnegative = nonNegative leftNonnegative
        in ℚₚ.*-monoʳ-≤-nonNeg left leftBelowRight
      second =
        let instance rightIsNonnegative = nonNegative rightNonnegative
        in ℚₚ.*-monoˡ-≤-nonNeg right leftBelowRight
    in
    ℚₚ.≤-trans first second

  beginLeft :
    (exponent : Nat) →
    L2.square
      (Prefix.prefixCount exponent * Geo.pow Geo.quarter exponent)
    ≡ L2.square (Prefix.prefixCount exponent)
        * Geo.pow sixteenth exponent
  beginLeft exponent =
    let
      quarterSquare :
        Geo.pow Geo.quarter exponent * Geo.pow Geo.quarter exponent
        ≡ Geo.pow sixteenth exponent
      quarterSquare = powerProduct Geo.quarter Geo.quarter exponent
    in
    subst
      (λ power →
        L2.square
          (Prefix.prefixCount exponent * Geo.pow Geo.quarter exponent)
        ≡ L2.square (Prefix.prefixCount exponent) * power)
      quarterSquare
      (solve
        ( Prefix.prefixCount exponent
        ∷ Geo.pow Geo.quarter exponent
        ∷ []
        ))

  open import Relation.Binary.PropositionalEquality using (subst₂)
