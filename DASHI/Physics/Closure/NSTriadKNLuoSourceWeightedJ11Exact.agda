module DASHI.Physics.Closure.NSTriadKNLuoSourceWeightedJ11Exact where

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
-- PURPOSE
-- Prove the literal weighted Jensen step in Luo's Section 4 estimate for J11.
-- If a_r denotes the square-safe normalized amplitude
--
--   a_r = lambda_r^(3/2) ||u_r||_2,
--
-- then the source summand is lambda_r a_r and its weighted square energy is
-- lambda_r a_r^2 = lambda_r^4 ||u_r||_2^2.  The finite weighted variance
-- identity gives
--
--   (sum_{r=0}^q lambda_r a_r)^2
--     <= (sum_{r=0}^q lambda_r)
--        (sum_{r=0}^q lambda_r a_r^2).
--
-- Exact dyadic induction proves sum_{r=0}^q lambda_r <= 2 lambda_q, yielding
-- the source-faithful square estimate with one explicit harmless constant 2.
-- No square root or J11 bound is postulated.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; subst₂)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Sum
import DASHI.Physics.Closure.NSTriadKNLuoFinitePrefixJensenExact as Prefix
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedJensenExact as Weighted

lambda : Nat → ℚ
lambda = Prefix.powTwo

two : ℚ
two = Prefix.two

prefixWeightedSamples : (Nat → ℚ) → Nat → List Weighted.WeightedValue
prefixWeightedSamples normalizedAmplitude zero =
  Weighted.weighted
    (lambda zero)
    (normalizedAmplitude zero)
    (Prefix.powTwoNonnegative zero)
  ∷ []
prefixWeightedSamples normalizedAmplitude (suc cutoff) =
  Weighted.weighted
    (lambda (suc cutoff))
    (normalizedAmplitude (suc cutoff))
    (Prefix.powTwoNonnegative (suc cutoff))
  ∷ prefixWeightedSamples normalizedAmplitude cutoff

dyadicPrefixMass : Nat → ℚ
dyadicPrefixMass zero = 1ℚ
dyadicPrefixMass (suc cutoff) =
  lambda (suc cutoff) + dyadicPrefixMass cutoff

prefixMassAgreement :
  (normalizedAmplitude : Nat → ℚ) →
  (cutoff : Nat) →
  Weighted.mass (prefixWeightedSamples normalizedAmplitude cutoff)
  ≡ dyadicPrefixMass cutoff
prefixMassAgreement normalizedAmplitude zero = refl
prefixMassAgreement normalizedAmplitude (suc cutoff)
  rewrite prefixMassAgreement normalizedAmplitude cutoff = refl

sourceAmplitude : (Nat → ℚ) → Nat → ℚ
sourceAmplitude normalizedAmplitude shell =
  lambda shell * normalizedAmplitude shell

sourceSquareEnergy : (Nat → ℚ) → Nat → ℚ
sourceSquareEnergy normalizedAmplitude shell =
  lambda shell * L2.square (normalizedAmplitude shell)

prefixFirstMomentAgreement :
  (normalizedAmplitude : Nat → ℚ) →
  (cutoff : Nat) →
  Weighted.firstMoment
    (prefixWeightedSamples normalizedAmplitude cutoff)
  ≡ Sum.sumTo (sourceAmplitude normalizedAmplitude) cutoff
prefixFirstMomentAgreement normalizedAmplitude zero = refl
prefixFirstMomentAgreement normalizedAmplitude (suc cutoff)
  rewrite prefixFirstMomentAgreement normalizedAmplitude cutoff = refl

prefixSecondMomentAgreement :
  (normalizedAmplitude : Nat → ℚ) →
  (cutoff : Nat) →
  Weighted.secondMoment
    (prefixWeightedSamples normalizedAmplitude cutoff)
  ≡ Sum.sumTo (sourceSquareEnergy normalizedAmplitude) cutoff
prefixSecondMomentAgreement normalizedAmplitude zero = refl
prefixSecondMomentAgreement normalizedAmplitude (suc cutoff)
  rewrite prefixSecondMomentAgreement normalizedAmplitude cutoff = refl

dyadicPrefixMassBelowTwiceTop :
  (cutoff : Nat) →
  dyadicPrefixMass cutoff ≤ two * lambda cutoff
dyadicPrefixMassBelowTwiceTop zero = Prefix.oneBelowPowTwo (suc zero)
dyadicPrefixMassBelowTwiceTop (suc cutoff) =
  let
    induction :
      dyadicPrefixMass cutoff ≤ two * lambda cutoff
    induction = dyadicPrefixMassBelowTwiceTop cutoff

    addTop :
      lambda (suc cutoff) + dyadicPrefixMass cutoff
      ≤ lambda (suc cutoff) + two * lambda cutoff
    addTop = ℚₚ.+-mono-≤ ℚₚ.≤-refl induction

    targetMeaning :
      lambda (suc cutoff) + two * lambda cutoff
      ≡ two * lambda (suc cutoff)
    targetMeaning = solve (two ∷ lambda cutoff ∷ [])
  in
  subst
    (λ upper → dyadicPrefixMass (suc cutoff) ≤ upper)
    targetMeaning
    addTop

sourceSquareEnergyNonnegative :
  (normalizedAmplitude : Nat → ℚ) →
  (shell : Nat) →
  0ℚ ≤ sourceSquareEnergy normalizedAmplitude shell
sourceSquareEnergyNonnegative normalizedAmplitude shell =
  let
    instance
      weightIsNonnegative =
        nonNegative (Prefix.powTwoNonnegative shell)
      squareIsNonnegative =
        nonNegative
          (L2.squareNonnegative (normalizedAmplitude shell))
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (lambda shell)
          (L2.square (normalizedAmplitude shell))
  in
  ℚₚ.nonNegative⁻¹
    (sourceSquareEnergy normalizedAmplitude shell)

prefixSourceSquareEnergyNonnegative :
  (normalizedAmplitude : Nat → ℚ) →
  (cutoff : Nat) →
  0ℚ ≤ Sum.sumTo (sourceSquareEnergy normalizedAmplitude) cutoff
prefixSourceSquareEnergyNonnegative normalizedAmplitude cutoff =
  Sum.sumToNonnegative
    (sourceSquareEnergy normalizedAmplitude)
    cutoff
    (sourceSquareEnergyNonnegative normalizedAmplitude)

sourceWeightedJ11SquareBound :
  (normalizedAmplitude : Nat → ℚ) →
  (outputShell : Nat) →
  L2.square
    (Sum.sumTo (sourceAmplitude normalizedAmplitude) outputShell)
  ≤ (two * lambda outputShell)
      * Sum.sumTo (sourceSquareEnergy normalizedAmplitude) outputShell
sourceWeightedJ11SquareBound normalizedAmplitude outputShell =
  let
    samples = prefixWeightedSamples normalizedAmplitude outputShell

    jensen :
      L2.square (Weighted.firstMoment samples)
      ≤ Weighted.mass samples * Weighted.secondMoment samples
    jensen = Weighted.finiteWeightedJensenSquare samples

    translatedJensen :
      L2.square
        (Sum.sumTo (sourceAmplitude normalizedAmplitude) outputShell)
      ≤ dyadicPrefixMass outputShell
          * Sum.sumTo
              (sourceSquareEnergy normalizedAmplitude)
              outputShell
    translatedJensen =
      subst₂ _≤_
        (cong L2.square
          (prefixFirstMomentAgreement normalizedAmplitude outputShell))
        (cong₂ _*_
          (prefixMassAgreement normalizedAmplitude outputShell)
          (prefixSecondMomentAgreement normalizedAmplitude outputShell))
        jensen

    massScaled :
      dyadicPrefixMass outputShell
        * Sum.sumTo
            (sourceSquareEnergy normalizedAmplitude)
            outputShell
      ≤ (two * lambda outputShell)
          * Sum.sumTo
              (sourceSquareEnergy normalizedAmplitude)
              outputShell
    massScaled =
      let
        instance
          energyIsNonnegative =
            nonNegative
              (prefixSourceSquareEnergyNonnegative
                normalizedAmplitude outputShell)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        (Sum.sumTo
          (sourceSquareEnergy normalizedAmplitude)
          outputShell)
        (dyadicPrefixMassBelowTwiceTop outputShell)
  in
  ℚₚ.≤-trans translatedJensen massScaled
