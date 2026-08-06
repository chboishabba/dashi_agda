module DASHI.Physics.YangMills.BalabanP33PrimitiveAbsoluteOperatorAdapterExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics, 1995 reprint.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Remove six independently supplied signed-coordinate bounds from the P33
-- primitive data.  A physical matrix coefficient now supplies only its exact
-- scalar value, an operator norm, and the standard domination
--
--   |matrix coefficient| <= operator norm.
--
-- Rational order then proves
--
--   -operator norm <= matrix coefficient <= operator norm,
--
-- and constructs the primitive five-mechanism input used downstream.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT3ConfiguredGeometricConstantsExact as Constants
import DASHI.Physics.YangMills.BalabanP33PrimitiveOperatorNormLocalBoundsExact as Primitive

------------------------------------------------------------------------
-- Exact rational absolute-value interval.
------------------------------------------------------------------------

valueBelowAbsolute : ∀ value → value ≤ ∣ value ∣
valueBelowAbsolute value with ℚP.≤-total 0ℚ value
... | inj₁ nonnegative =
  subst
    (λ upper → value ≤ upper)
    (sym (ℚP.0≤p⇒∣p∣≡p nonnegative))
    ℚP.≤-refl
... | inj₂ nonpositive =
  let
    negativeNonnegative : 0ℚ ≤ - value
    negativeNonnegative = ℚP.neg-antimono-≤ nonpositive

    absoluteIsNegative : ∣ value ∣ ≡ - value
    absoluteIsNegative =
      trans
        (sym (ℚP.∣-p∣≡∣p∣ value))
        (ℚP.0≤p⇒∣p∣≡p negativeNonnegative)
  in
  subst
    (λ upper → value ≤ upper)
    (sym absoluteIsNegative)
    (ℚP.≤-trans nonpositive negativeNonnegative)

doubleNegation : ∀ value → - (- value) ≡ value
doubleNegation = ℚRing.solve-∀

negativeAbsoluteBelowValue : ∀ value → - ∣ value ∣ ≤ value
negativeAbsoluteBelowValue value =
  subst
    (λ upper → - ∣ value ∣ ≤ upper)
    (doubleNegation value)
    (ℚP.neg-antimono-≤
      (subst
        (λ upper → - value ≤ upper)
        (ℚP.∣-p∣≡∣p∣ value)
        (valueBelowAbsolute (- value))))

absoluteTwoSided : ∀ value →
  Primitive.TwoSided value ∣ value ∣
absoluteTwoSided value = record
  { Primitive.TwoSided.lower = negativeAbsoluteBelowValue value
  ; Primitive.TwoSided.upper = valueBelowAbsolute value
  }

operatorNormDominatesCoordinate :
  ∀ value operatorNorm →
  ∣ value ∣ ≤ operatorNorm →
  Primitive.TwoSided value operatorNorm
operatorNormDominatesCoordinate value operatorNorm absoluteBound =
  Primitive.tightenTwoSided
    value ∣ value ∣ operatorNorm absoluteBound
    (absoluteTwoSided value)

------------------------------------------------------------------------
-- Physical primitive data with coordinate domination derived, not supplied.
------------------------------------------------------------------------

record PrimitiveAbsoluteOperatorNorms (Cell : Set) : Set₁ where
  field
    radius : ℚ
    radiusNonnegative : 0ℚ ≤ radius

    adDefect dexpDefect inverseDexpDefect : Cell → ℚ
    covariantDefect covariantAdjointDefect blockDerivativeDefect : Cell → ℚ

    adNorm dexpNorm inverseDexpNorm : Cell → ℚ
    covariantNorm covariantAdjointNorm blockDerivativeNorm : Cell → ℚ

    adAbsoluteBelowNorm : ∀ cell →
      ∣ adDefect cell ∣ ≤ adNorm cell
    dexpAbsoluteBelowNorm : ∀ cell →
      ∣ dexpDefect cell ∣ ≤ dexpNorm cell
    inverseDexpAbsoluteBelowNorm : ∀ cell →
      ∣ inverseDexpDefect cell ∣ ≤ inverseDexpNorm cell
    covariantAbsoluteBelowNorm : ∀ cell →
      ∣ covariantDefect cell ∣ ≤ covariantNorm cell
    covariantAdjointAbsoluteBelowNorm : ∀ cell →
      ∣ covariantAdjointDefect cell ∣ ≤ covariantAdjointNorm cell
    blockDerivativeAbsoluteBelowNorm : ∀ cell →
      ∣ blockDerivativeDefect cell ∣ ≤ blockDerivativeNorm cell

    adOperatorBound : ∀ cell →
      adNorm cell ≤ radius

    dexpPairOperatorBound : ∀ cell →
      dexpNorm cell + inverseDexpNorm cell
      ≤ Constants.twoℚ * radius

    covariantPairOperatorBound : ∀ cell →
      covariantNorm cell + covariantAdjointNorm cell
      ≤ Constants.twoℚ * radius

    blockDerivativeOperatorBound : ∀ cell →
      blockDerivativeNorm cell ≤ radius

open PrimitiveAbsoluteOperatorNorms public

asPrimitivePhysicalOperatorNorms :
  ∀ {Cell} →
  PrimitiveAbsoluteOperatorNorms Cell →
  Primitive.PrimitivePhysicalOperatorNorms Cell
asPrimitivePhysicalOperatorNorms dataSet = record
  { Primitive.PrimitivePhysicalOperatorNorms.radius = radius dataSet
  ; Primitive.PrimitivePhysicalOperatorNorms.radiusNonnegative =
      radiusNonnegative dataSet
  ; Primitive.PrimitivePhysicalOperatorNorms.adDefect = adDefect dataSet
  ; Primitive.PrimitivePhysicalOperatorNorms.dexpDefect = dexpDefect dataSet
  ; Primitive.PrimitivePhysicalOperatorNorms.inverseDexpDefect =
      inverseDexpDefect dataSet
  ; Primitive.PrimitivePhysicalOperatorNorms.covariantDefect =
      covariantDefect dataSet
  ; Primitive.PrimitivePhysicalOperatorNorms.covariantAdjointDefect =
      covariantAdjointDefect dataSet
  ; Primitive.PrimitivePhysicalOperatorNorms.blockDerivativeDefect =
      blockDerivativeDefect dataSet
  ; Primitive.PrimitivePhysicalOperatorNorms.adNorm = adNorm dataSet
  ; Primitive.PrimitivePhysicalOperatorNorms.dexpNorm = dexpNorm dataSet
  ; Primitive.PrimitivePhysicalOperatorNorms.inverseDexpNorm =
      inverseDexpNorm dataSet
  ; Primitive.PrimitivePhysicalOperatorNorms.covariantNorm =
      covariantNorm dataSet
  ; Primitive.PrimitivePhysicalOperatorNorms.covariantAdjointNorm =
      covariantAdjointNorm dataSet
  ; Primitive.PrimitivePhysicalOperatorNorms.blockDerivativeNorm =
      blockDerivativeNorm dataSet
  ; Primitive.PrimitivePhysicalOperatorNorms.adCoordinateBound =
      λ cell → operatorNormDominatesCoordinate
        (adDefect dataSet cell) (adNorm dataSet cell)
        (adAbsoluteBelowNorm dataSet cell)
  ; Primitive.PrimitivePhysicalOperatorNorms.dexpCoordinateBound =
      λ cell → operatorNormDominatesCoordinate
        (dexpDefect dataSet cell) (dexpNorm dataSet cell)
        (dexpAbsoluteBelowNorm dataSet cell)
  ; Primitive.PrimitivePhysicalOperatorNorms.inverseDexpCoordinateBound =
      λ cell → operatorNormDominatesCoordinate
        (inverseDexpDefect dataSet cell) (inverseDexpNorm dataSet cell)
        (inverseDexpAbsoluteBelowNorm dataSet cell)
  ; Primitive.PrimitivePhysicalOperatorNorms.covariantCoordinateBound =
      λ cell → operatorNormDominatesCoordinate
        (covariantDefect dataSet cell) (covariantNorm dataSet cell)
        (covariantAbsoluteBelowNorm dataSet cell)
  ; Primitive.PrimitivePhysicalOperatorNorms.covariantAdjointCoordinateBound =
      λ cell → operatorNormDominatesCoordinate
        (covariantAdjointDefect dataSet cell)
        (covariantAdjointNorm dataSet cell)
        (covariantAdjointAbsoluteBelowNorm dataSet cell)
  ; Primitive.PrimitivePhysicalOperatorNorms.blockDerivativeCoordinateBound =
      λ cell → operatorNormDominatesCoordinate
        (blockDerivativeDefect dataSet cell)
        (blockDerivativeNorm dataSet cell)
        (blockDerivativeAbsoluteBelowNorm dataSet cell)
  ; Primitive.PrimitivePhysicalOperatorNorms.adOperatorBound =
      adOperatorBound dataSet
  ; Primitive.PrimitivePhysicalOperatorNorms.dexpPairOperatorBound =
      dexpPairOperatorBound dataSet
  ; Primitive.PrimitivePhysicalOperatorNorms.covariantPairOperatorBound =
      covariantPairOperatorBound dataSet
  ; Primitive.PrimitivePhysicalOperatorNorms.blockDerivativeOperatorBound =
      blockDerivativeOperatorBound dataSet
  }

rationalAbsoluteIntervalLevel : ProofLevel
rationalAbsoluteIntervalLevel = machineChecked

operatorNormToSignedCoordinateLevel : ProofLevel
operatorNormToSignedCoordinateLevel = machineChecked

primitiveAbsoluteAdapterLevel : ProofLevel
primitiveAbsoluteAdapterLevel = machineChecked
