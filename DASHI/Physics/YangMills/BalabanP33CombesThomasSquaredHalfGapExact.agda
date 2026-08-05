module DASHI.Physics.YangMills.BalabanP33CombesThomasSquaredHalfGapExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Werner Kirsch,
-- "An Invitation to Random Schrödinger Operators",
-- Panoramas et Synthèses 25 (2008), 1--119; arXiv:0709.3707.
-- No DOI was assigned to the cited survey chapter.
--
-- Zhongwei Shen,
-- "An Improved Combes--Thomas Estimate of Magnetic Schrödinger Operators",
-- Arkiv för Matematik 52 (2014), 383--414.
-- DOI: 10.1007/s11512-013-0191-2.
--
-- DASHI CONTRIBUTION
--
-- Formalize the half-gap argument entirely in squared finite rational norms.
-- This avoids requiring a Bishop square-root backend merely to transport the
-- P33 coercive floor through the non-self-adjoint diagonal conjugation.
--
-- If
--
--   4 h2 ||x||^2 <= ||H x||^2,
--       ||E x||^2 <= h2 ||x||^2,
--       ||H x||^2 <= 2 ||(H+E)x||^2 + 2 ||E x||^2,
--
-- then
--
--       h2 ||x||^2 <= ||(H+E)x||^2.
--
-- At delta=1/32, h2=(delta/2)^2=1/4096.  Hence the tilted inverse has squared
-- norm factor 4096 and unsquared factor 64=2/delta, matching the standard
-- textbook prefactor.  Shen's trace-ideal and faster-than-polynomial
-- refinements are explicitly out of scope for this finite matrix theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_; _/_; NonNegative; Positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33FiniteCombesThomasTiltBudgetExact as Tilt

------------------------------------------------------------------------
-- Scalar squared half-gap arithmetic.
------------------------------------------------------------------------

halfGapSquaredSurvives :
  ∀ halfGapSquared normX normHX normEX normTiltedX →
  ((+ 4 / 1) * halfGapSquared) * normX ≤ normHX →
  normEX ≤ halfGapSquared * normX →
  normHX
    ≤ (+ 2 / 1) * normTiltedX + (+ 2 / 1) * normEX →
  halfGapSquared * normX ≤ normTiltedX
halfGapSquaredSurvives
    halfGapSquared normX normHX normEX normTiltedX
    originalLower perturbationUpper reverseTriangleSquared =
  let
    twoNonnegative : 0ℚ ≤ (+ 2 / 1)
    twoNonnegative = ℚP.nonNegative⁻¹ (+ 2 / 1)

    instance
      twoNN : NonNegative (+ 2 / 1)
      twoNN = ℚ.nonNegative twoNonnegative

    defectScaled :
      (+ 2 / 1) * normEX
      ≤ (+ 2 / 1) * (halfGapSquared * normX)
    defectScaled =
      ℚP.*-monoˡ-≤-nonNeg (+ 2 / 1) perturbationUpper

    defectSubstituted :
      normHX
      ≤ (+ 2 / 1) * normTiltedX
        + (+ 2 / 1) * (halfGapSquared * normX)
    defectSubstituted =
      ℚP.≤-trans
        reverseTriangleSquared
        (ℚP.+-mono-≤ ℚP.≤-refl defectScaled)

    originalIntoTilt :
      ((+ 4 / 1) * halfGapSquared) * normX
      ≤ (+ 2 / 1) * normTiltedX
        + (+ 2 / 1) * (halfGapSquared * normX)
    originalIntoTilt =
      ℚP.≤-trans originalLower defectSubstituted

    shifted :
      (((+ 4 / 1) * halfGapSquared) * normX)
        + (0ℚ - ((+ 2 / 1) * (halfGapSquared * normX)))
      ≤ ((+ 2 / 1) * normTiltedX
          + (+ 2 / 1) * (halfGapSquared * normX))
        + (0ℚ - ((+ 2 / 1) * (halfGapSquared * normX)))
    shifted =
      ℚP.+-mono-≤ originalIntoTilt ℚP.≤-refl

    reduced :
      ((+ 2 / 1) * halfGapSquared) * normX
      ≤ (+ 2 / 1) * normTiltedX
    reduced =
      subst
        (λ lower → lower ≤ (+ 2 / 1) * normTiltedX)
        (ℚRing.solve-∀ halfGapSquared normX)
        (subst
          (λ upper →
            (((+ 4 / 1) * halfGapSquared) * normX)
              + (0ℚ - ((+ 2 / 1) * (halfGapSquared * normX)))
            ≤ upper)
          (ℚRing.solve-∀ normTiltedX halfGapSquared normX)
          shifted)

    cancelledShape :
      (+ 2 / 1) * (halfGapSquared * normX)
      ≤ (+ 2 / 1) * normTiltedX
    cancelledShape =
      subst
        (λ lower → lower ≤ (+ 2 / 1) * normTiltedX)
        (ℚRing.solve-∀ halfGapSquared normX)
        reduced

    twoPositiveProof : 0ℚ < (+ 2 / 1)
    twoPositiveProof = ℚP.positive⁻¹ (+ 2 / 1)

    instance
      twoPositive : Positive (+ 2 / 1)
      twoPositive = ℚ.positive twoPositiveProof
  in
  ℚP.*-cancelˡ-≤-pos (+ 2 / 1) cancelledShape

------------------------------------------------------------------------
-- The exact P33 calibration.
------------------------------------------------------------------------

p33HalfGapSquared : ℚ
p33HalfGapSquared = + 1 / 4096

p33OriginalGapSquared : ℚ
p33OriginalGapSquared = + 1 / 1024

p33HalfGapSquaredTimesFour :
  (+ 4 / 1) * p33HalfGapSquared ≡ p33OriginalGapSquared
p33HalfGapSquaredTimesFour = ℚRing.solve []

p33HalfGapSquaredIsOneOverSixtyFourSquared :
  p33HalfGapSquared
  ≡ Tilt.p33HalfGap * Tilt.p33HalfGap
p33HalfGapSquaredIsOneOverSixtyFourSquared = ℚRing.solve []

p33OriginalGapSquaredIsOneOverThirtyTwoSquared :
  p33OriginalGapSquared
  ≡ Tilt.p33SpectralGap * Tilt.p33SpectralGap
p33OriginalGapSquaredIsOneOverThirtyTwoSquared = ℚRing.solve []

p33SquaredHalfGapSurvives :
  ∀ normX normHX normEX normTiltedX →
  p33OriginalGapSquared * normX ≤ normHX →
  normEX ≤ p33HalfGapSquared * normX →
  normHX
    ≤ (+ 2 / 1) * normTiltedX + (+ 2 / 1) * normEX →
  p33HalfGapSquared * normX ≤ normTiltedX
p33SquaredHalfGapSurvives
    normX normHX normEX normTiltedX
    originalLower perturbationUpper reverseTriangleSquared =
  halfGapSquaredSurvives
    p33HalfGapSquared normX normHX normEX normTiltedX
    (subst
      (λ coefficient → coefficient * normX ≤ normHX)
      (sym p33HalfGapSquaredTimesFour)
      originalLower)
    perturbationUpper
    reverseTriangleSquared

p33SquaredInverseScale : ℚ
p33SquaredInverseScale = + 4096 / 1

p33SquaredInverseScaleNonnegative : 0ℚ ≤ p33SquaredInverseScale
p33SquaredInverseScaleNonnegative =
  ℚP.nonNegative⁻¹ p33SquaredInverseScale

p33SquaredRescaling : ∀ value →
  p33SquaredInverseScale * (p33HalfGapSquared * value) ≡ value
p33SquaredRescaling = ℚRing.solve-∀

p33TiltedInverseSquaredBound :
  ∀ inverseNormSq outputNormSq →
  p33HalfGapSquared * inverseNormSq ≤ outputNormSq →
  inverseNormSq ≤ p33SquaredInverseScale * outputNormSq
p33TiltedInverseSquaredBound
    inverseNormSq outputNormSq lowerBound =
  let
    instance
      scaleNN : NonNegative p33SquaredInverseScale
      scaleNN = ℚ.nonNegative p33SquaredInverseScaleNonnegative

    scaled :
      p33SquaredInverseScale
        * (p33HalfGapSquared * inverseNormSq)
      ≤ p33SquaredInverseScale * outputNormSq
    scaled =
      ℚP.*-monoˡ-≤-nonNeg p33SquaredInverseScale lowerBound
  in
  subst
    (λ lower → lower ≤ p33SquaredInverseScale * outputNormSq)
    (p33SquaredRescaling inverseNormSq)
    scaled

------------------------------------------------------------------------
-- Same-vector operator identity and squared reverse triangle.
------------------------------------------------------------------------

matrixDifference :
  ∀ {Index : Set} →
  Schur.Matrix Index → Schur.Matrix Index → Schur.Matrix Index
matrixDifference tilted original row column =
  tilted row column - original row column

sumNegate :
  ∀ {Index : Set}
    (indices : List Index) (term : Index → ℚ) →
  Sums.sumRational indices (λ index → 0ℚ - term index)
  ≡ 0ℚ - Sums.sumRational indices term
sumNegate [] term = refl
sumNegate (index ∷ indices) term
  rewrite sumNegate indices term = ℚRing.solve []

matrixDifferenceApplyExact :
  ∀ {Index : Set}
    (indices : List Index)
    (tilted original : Schur.Matrix Index)
    (vector : Schur.Vector Index)
    (row : Index) →
  Schur.matrixApply indices
    (matrixDifference tilted original) vector row
  ≡ Schur.matrixApply indices tilted vector row
    - Schur.matrixApply indices original vector row
matrixDifferenceApplyExact indices tilted original vector row =
  trans
    (Sums.sumRationalCong
      indices
      (λ column →
        (tilted row column - original row column) * vector column)
      (λ column →
        tilted row column * vector column
        + (0ℚ - original row column * vector column))
      (λ column → ℚRing.solve []))
    (trans
      (Fubini.sumRationalAdd
        indices
        (λ column → tilted row column * vector column)
        (λ column → 0ℚ - original row column * vector column))
      (trans
        (cong
          (Schur.matrixApply indices tilted vector row +_)
          (sumNegate
            indices
            (λ column → original row column * vector column)))
        (ℚRing.solve-∀
          (Schur.matrixApply indices tilted vector row)
          (Schur.matrixApply indices original vector row))))

sameVectorTiltDecomposition :
  ∀ {Index : Set}
    (indices : List Index)
    (tilted original : Schur.Matrix Index)
    (vector : Schur.Vector Index)
    (row : Index) →
  Schur.matrixApply indices tilted vector row
  ≡ Schur.matrixApply indices original vector row
    + Schur.matrixApply indices
        (matrixDifference tilted original) vector row
sameVectorTiltDecomposition
    indices tilted original vector row =
  let
    differenceExact =
      matrixDifferenceApplyExact indices tilted original vector row
  in
  trans
    (ℚRing.solve-∀
      (Schur.matrixApply indices tilted vector row)
      (Schur.matrixApply indices original vector row))
    (cong
      (Schur.matrixApply indices original vector row +_)
      (sym differenceExact))

scalarDifferenceSquareBelowDouble : ∀ left right →
  FiniteL2.square (left - right)
  ≤ (+ 2 / 1) * FiniteL2.square left
    + (+ 2 / 1) * FiniteL2.square right
scalarDifferenceSquareBelowDouble left right =
  let
    decomposition :
      (+ 2 / 1) * FiniteL2.square left
        + (+ 2 / 1) * FiniteL2.square right
      ≡ FiniteL2.square (left - right)
        + FiniteL2.square (left + right)
    decomposition = ℚRing.solve []

    addNonnegative :
      FiniteL2.square (left - right)
      ≤ FiniteL2.square (left - right)
        + FiniteL2.square (left + right)
    addNonnegative =
      let
        instance
          tailNN : NonNegative (FiniteL2.square (left + right))
          tailNN = ℚ.nonNegative
            (FiniteL2.squareNonnegative (left + right))
      in
      ℚP.p≤p+q
        (FiniteL2.square (left - right))
        (FiniteL2.square (left + right))
  in
  subst
    (λ upper → FiniteL2.square (left - right) ≤ upper)
    (sym decomposition)
    addNonnegative

vectorDifferenceNormSqBelowDouble :
  ∀ {Index : Set}
    (indices : List Index)
    (left right : Schur.Vector Index) →
  Schur.vectorNormSq indices (λ index → left index - right index)
  ≤ (+ 2 / 1) * Schur.vectorNormSq indices left
    + (+ 2 / 1) * Schur.vectorNormSq indices right
vectorDifferenceNormSqBelowDouble indices left right =
  trans
    (Schur.sumPointwiseBelow
      indices
      (λ index → FiniteL2.square (left index - right index))
      (λ index →
        (+ 2 / 1) * FiniteL2.square (left index)
        + (+ 2 / 1) * FiniteL2.square (right index))
      (λ index → scalarDifferenceSquareBelowDouble
        (left index) (right index)))
    (trans
      (Fubini.sumRationalAdd
        indices
        (λ index → (+ 2 / 1) * FiniteL2.square (left index))
        (λ index → (+ 2 / 1) * FiniteL2.square (right index)))
      (cong₂ _+_
        (Sums.sumRationalScale
          (+ 2 / 1) indices
          (λ index → FiniteL2.square (left index)))
        (Sums.sumRationalScale
          (+ 2 / 1) indices
          (λ index → FiniteL2.square (right index)))))

sameVectorReverseTriangleSquared :
  ∀ {Index : Set}
    (indices : List Index)
    (tilted original : Schur.Matrix Index)
    (vector : Schur.Vector Index) →
  Schur.vectorNormSq indices
    (Schur.matrixApply indices original vector)
  ≤ (+ 2 / 1)
      * Schur.vectorNormSq indices
          (Schur.matrixApply indices tilted vector)
    + (+ 2 / 1)
      * Schur.vectorNormSq indices
          (Schur.matrixApply indices
            (matrixDifference tilted original) vector)
sameVectorReverseTriangleSquared
    indices tilted original vector =
  let
    originalAsDifference : ∀ row →
      Schur.matrixApply indices original vector row
      ≡ Schur.matrixApply indices tilted vector row
        - Schur.matrixApply indices
            (matrixDifference tilted original) vector row
    originalAsDifference row =
      let
        decomposition =
          sameVectorTiltDecomposition
            indices tilted original vector row
      in
      subst
        (λ selected →
          Schur.matrixApply indices original vector row
          ≡ selected
            - Schur.matrixApply indices
                (matrixDifference tilted original) vector row)
        (sym decomposition)
        (ℚRing.solve-∀
          (Schur.matrixApply indices original vector row)
          (Schur.matrixApply indices
            (matrixDifference tilted original) vector row))

    normRewrite :
      Schur.vectorNormSq indices
        (Schur.matrixApply indices original vector)
      ≡ Schur.vectorNormSq indices
          (λ row →
            Schur.matrixApply indices tilted vector row
            - Schur.matrixApply indices
                (matrixDifference tilted original) vector row)
    normRewrite =
      Sums.sumRationalCong
        indices
        (λ row →
          FiniteL2.square
            (Schur.matrixApply indices original vector row))
        (λ row →
          FiniteL2.square
            (Schur.matrixApply indices tilted vector row
              - Schur.matrixApply indices
                  (matrixDifference tilted original) vector row))
        (λ row → cong FiniteL2.square (originalAsDifference row))
  in
  subst
    (λ lower →
      lower
      ≤ (+ 2 / 1)
          * Schur.vectorNormSq indices
              (Schur.matrixApply indices tilted vector)
        + (+ 2 / 1)
          * Schur.vectorNormSq indices
              (Schur.matrixApply indices
                (matrixDifference tilted original) vector))
    (sym normRewrite)
    (vectorDifferenceNormSqBelowDouble
      indices
      (Schur.matrixApply indices tilted vector)
      (Schur.matrixApply indices
        (matrixDifference tilted original) vector))

combesThomasSquaredHalfGapLevel : ProofLevel
combesThomasSquaredHalfGapLevel = machineChecked

p33SquaredInverseFactor4096Level : ProofLevel
p33SquaredInverseFactor4096Level = machineChecked

sameVectorTiltIdentityLevel : ProofLevel
sameVectorTiltIdentityLevel = machineChecked

sameVectorReverseTriangleSquaredLevel : ProofLevel
sameVectorReverseTriangleSquaredLevel = machineChecked
