module DASHI.Physics.Closure.NSTriadKNLuoFiniteArbitraryPolynomialAbsorptionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Darko Mitrović.
-- Title: "A High-Frequency Tail Condition and a Diagnostic Iteration for
-- the Navier--Stokes Equations".
-- arXiv:2411.02568.
-- DOI: none assigned in the cited preprint version.
--
-- Mathematical ingredient: every fixed finite power of a nonnegative
-- quantity preserves an established order bound.
--
-- PURPOSE
-- Upgrade the round-six one-factor estimate
--
--   (n+1) 4^{-n} <= 2^{-n}
--
-- to every finite polynomial degree m:
--
--   ((n+1) 4^{-n})^m <= (2^{-n})^m.
--
-- This is a checked dyadic version of exponential-to-polynomial absorption.
-- It does not identify the rational geometric factor with the continuum
-- exponential exp(-c lambda_q^epsilon).
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNLuoFiniteExponentialPolynomialAbsorptionExact as Linear
import DASHI.Physics.Closure.NSTriadKNLuoFinitePrefixJensenExact as Prefix
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

powerMonotone :
  (left right : ℚ) →
  0ℚ ≤ left →
  0ℚ ≤ right →
  left ≤ right →
  (degree : Nat) →
  Geo.pow left degree ≤ Geo.pow right degree
powerMonotone left right leftNonnegative rightNonnegative leftBelowRight zero =
  ℚₚ.≤-refl
powerMonotone left right leftNonnegative rightNonnegative leftBelowRight
  (suc degree) =
  let
    leftPowerNonnegative =
      Geo.powNonnegative left degree leftNonnegative

    first :
      left * Geo.pow left degree
      ≤ right * Geo.pow left degree
    first =
      let
        instance
          leftPowerIsNonnegative = nonNegative leftPowerNonnegative
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (Geo.pow left degree)
        leftBelowRight

    second :
      right * Geo.pow left degree
      ≤ right * Geo.pow right degree
    second =
      let
        instance
          rightIsNonnegative = nonNegative rightNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        right
        (powerMonotone
          left right
          leftNonnegative rightNonnegative leftBelowRight degree)
  in
  ℚₚ.≤-trans first second

linearDampedFactor : Nat → ℚ
linearDampedFactor exponent =
  Prefix.prefixCount exponent * Geo.pow Geo.quarter exponent

halfDampedFactor : Nat → ℚ
halfDampedFactor exponent =
  Geo.pow Linear.half exponent

prefixCountNonnegative :
  (exponent : Nat) →
  0ℚ ≤ Prefix.prefixCount exponent
prefixCountNonnegative zero =
  toWitness {a? = 0ℚ ≤? 1ℚ} _
prefixCountNonnegative (suc exponent) =
  L2.addNonnegative
    (toWitness {a? = 0ℚ ≤? 1ℚ} _)
    (prefixCountNonnegative exponent)

halfNonnegative : 0ℚ ≤ Linear.half
halfNonnegative = toWitness {a? = 0ℚ ≤? Linear.half} _

linearDampedFactorNonnegative :
  (exponent : Nat) →
  0ℚ ≤ linearDampedFactor exponent
linearDampedFactorNonnegative exponent =
  let
    countNonnegative = prefixCountNonnegative exponent
    quarterPowerNonnegative =
      Geo.powNonnegative
        Geo.quarter exponent Geo.quarterNonnegative
    instance
      countIsNonnegative = nonNegative countNonnegative
      powerIsNonnegative = nonNegative quarterPowerNonnegative
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (Prefix.prefixCount exponent)
          (Geo.pow Geo.quarter exponent)
  in
  ℚₚ.nonNegative⁻¹ (linearDampedFactor exponent)

halfDampedFactorNonnegative :
  (exponent : Nat) →
  0ℚ ≤ halfDampedFactor exponent
halfDampedFactorNonnegative exponent =
  Geo.powNonnegative
    Linear.half exponent halfNonnegative

arbitraryPolynomialDegreeAbsorbed :
  (exponent degree : Nat) →
  Geo.pow (linearDampedFactor exponent) degree
  ≤ Geo.pow (halfDampedFactor exponent) degree
arbitraryPolynomialDegreeAbsorbed exponent degree =
  powerMonotone
    (linearDampedFactor exponent)
    (halfDampedFactor exponent)
    (linearDampedFactorNonnegative exponent)
    (halfDampedFactorNonnegative exponent)
    (Linear.linearMultiplicityAbsorbed exponent)
    degree
