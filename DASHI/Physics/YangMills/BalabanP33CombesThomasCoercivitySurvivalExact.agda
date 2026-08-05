module DASHI.Physics.YangMills.BalabanP33CombesThomasCoercivitySurvivalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Jan Swoboda,
-- "Morse Homology for the Yang--Mills Gradient Flow",
-- Journal de Mathematiques Pures et Appliquees 98 (2012), 160--210.
-- DOI: 10.1016/j.matpur.2012.02.001.
--
-- DASHI CONTRIBUTION
--
-- Isolate and prove the quantitative coercivity-survival step in the
-- Combes--Thomas conjugation argument.  Write
--
--   H_D = H + E.
--
-- If the original operator has the norm lower bound
--
--   2 h ||x|| <= ||H x||
--
-- and the tilt perturbation has
--
--   ||E x|| <= h ||x||,
--
-- then the reverse triangle inequality yields
--
--   h ||x|| <= ||H_D x||.
--
-- At the P33 floor 2h=1/32, one has h=1/64, hence every inverse of H_D
-- satisfies the explicit norm estimate
--
--   ||H_D^{-1} y|| <= 64 ||y|| = (2/delta)||y||.
--
-- This is the standard half-gap mechanism.  The proof below is exact ordered
-- rational arithmetic and does not invoke a custom local-parametrix residual.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasTiltBudgetExact as Tilt

------------------------------------------------------------------------
-- Generic scalar half-gap lemma.
------------------------------------------------------------------------

halfGapCoercivitySurvives :
  ∀ halfGap normX normHX normEX normTiltedX →
  ((+ 2 / 1) * halfGap) * normX ≤ normHX →
  normEX ≤ halfGap * normX →
  normHX ≤ normTiltedX + normEX →
  halfGap * normX ≤ normTiltedX
halfGapCoercivitySurvives
    halfGap normX normHX normEX normTiltedX
    originalLower perturbationUpper reverseTriangle =
  let
    hxBelowTiltPlusHalf :
      normHX ≤ normTiltedX + halfGap * normX
    hxBelowTiltPlusHalf =
      ℚP.≤-trans
        reverseTriangle
        (ℚP.+-mono-≤
          ℚP.≤-refl
          perturbationUpper)

    doubledHalfBelow :
      ((+ 2 / 1) * halfGap) * normX
      ≤ normTiltedX + halfGap * normX
    doubledHalfBelow =
      ℚP.≤-trans originalLower hxBelowTiltPlusHalf

    shifted :
      (((+ 2 / 1) * halfGap) * normX)
        + (0ℚ - halfGap * normX)
      ≤ (normTiltedX + halfGap * normX)
        + (0ℚ - halfGap * normX)
    shifted =
      ℚP.+-mono-≤
        doubledHalfBelow
        ℚP.≤-refl

    leftCancels :
      (((+ 2 / 1) * halfGap) * normX)
        + (0ℚ - halfGap * normX)
      ≡ halfGap * normX
    leftCancels = ℚRing.solve []

    rightCancels :
      (normTiltedX + halfGap * normX)
        + (0ℚ - halfGap * normX)
      ≡ normTiltedX
    rightCancels = ℚRing.solve []

    rightReduced :
      (((+ 2 / 1) * halfGap) * normX)
        + (0ℚ - halfGap * normX)
      ≤ normTiltedX
    rightReduced =
      subst
        (λ upper →
          (((+ 2 / 1) * halfGap) * normX)
            + (0ℚ - halfGap * normX)
          ≤ upper)
        rightCancels
        shifted
  in
  subst
    (λ lower → lower ≤ normTiltedX)
    leftCancels
    rightReduced

------------------------------------------------------------------------
-- P33 calibration delta=1/32, half-gap=1/64.
------------------------------------------------------------------------

p33OriginalGapAsTwoHalfGaps :
  ((+ 2 / 1) * Tilt.p33HalfGap) ≡ Tilt.p33SpectralGap
p33OriginalGapAsTwoHalfGaps = Tilt.p33HalfGapIsHalf

p33TiltedCoercivityFromHalfGap :
  ∀ normX normHX normEX normTiltedX →
  Tilt.p33SpectralGap * normX ≤ normHX →
  normEX ≤ Tilt.p33HalfGap * normX →
  normHX ≤ normTiltedX + normEX →
  Tilt.p33HalfGap * normX ≤ normTiltedX
p33TiltedCoercivityFromHalfGap
    normX normHX normEX normTiltedX
    originalLower perturbationUpper reverseTriangle =
  halfGapCoercivitySurvives
    Tilt.p33HalfGap normX normHX normEX normTiltedX
    (subst
      (λ coefficient → coefficient * normX ≤ normHX)
      (sym p33OriginalGapAsTwoHalfGaps)
      originalLower)
    perturbationUpper
    reverseTriangle

p33InverseScale : ℚ
p33InverseScale = + 64 / 1

p33InverseScaleNonnegative : 0ℚ ≤ p33InverseScale
p33InverseScaleNonnegative = ℚP.nonNegative⁻¹ p33InverseScale

p33HalfGapRescaling : ∀ value →
  p33InverseScale * (Tilt.p33HalfGap * value) ≡ value
p33HalfGapRescaling = ℚRing.solve-∀

p33TiltedInverseNormBound :
  ∀ inverseNorm outputNorm →
  Tilt.p33HalfGap * inverseNorm ≤ outputNorm →
  inverseNorm ≤ p33InverseScale * outputNorm
p33TiltedInverseNormBound inverseNorm outputNorm lowerBound =
  let
    instance
      scaleNN : NonNegative p33InverseScale
      scaleNN = ℚ.nonNegative p33InverseScaleNonnegative

    scaled :
      p33InverseScale * (Tilt.p33HalfGap * inverseNorm)
      ≤ p33InverseScale * outputNorm
    scaled =
      ℚP.*-monoˡ-≤-nonNeg p33InverseScale lowerBound
  in
  subst
    (λ lower → lower ≤ p33InverseScale * outputNorm)
    (p33HalfGapRescaling inverseNorm)
    scaled

p33TiltedInverseMajorantAgreesWithCalibration :
  p33InverseScale ≡ Tilt.p33TiltedResolventMajorant
p33TiltedInverseMajorantAgreesWithCalibration = ℚRing.solve []

combesThomasHalfGapSurvivalLevel : ProofLevel
combesThomasHalfGapSurvivalLevel = machineChecked

p33CombesThomasCoercivitySurvivalLevel : ProofLevel
p33CombesThomasCoercivitySurvivalLevel = machineChecked

p33CombesThomasInverse64Level : ProofLevel
p33CombesThomasInverse64Level = machineChecked
