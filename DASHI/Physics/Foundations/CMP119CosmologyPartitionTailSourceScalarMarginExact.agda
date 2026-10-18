{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPartitionTailSourceScalarMarginExact where

------------------------------------------------------------------------
-- B2 NORMALIZATION-FREE SOURCE MARGIN.
--
-- Suppose the selected finite partition derivative has the source form
--
--   D_Weyl Z = -(N_ERB + N_V),
--
-- with a common positive partition/density integral Z, and source analysis
-- supplies
--
--   N_ERB <= M_ERB * Z,
--   N_V   = c_V * Z.
--
-- Then the R109-tail condition
--
--   Tail * Z < D_Weyl Z
--
-- follows from the normalization-free scalar inequality
--
--   M_ERB + Tail < - c_V.
--
-- This is exactly the coefficient-level calculation wanted from the literal
-- Eq. (2.23) source.  It does not infer M_ERB or c_V; those are source
-- estimates.  It only proves that no separate numerical value or upper bound
-- for Z is required once every term shares the same positive density integral.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_; _<_; Positive; positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (subst; subst₂)

sourceScalarMarginForcesPartitionTailDominance :
  ∀ {z erbNumerator erbUpper vacuumCoefficient tail partitionDerivative : ℚ} →
  0ℚ < z →
  erbNumerator ≤ erbUpper * z →
  partitionDerivative ≡ - (erbNumerator + vacuumCoefficient * z) →
  erbUpper + tail < - vacuumCoefficient →
  tail * z < partitionDerivative
sourceScalarMarginForcesPartitionTailDominance
    {z} {erbNumerator} {erbUpper} {vacuumCoefficient} {tail}
    {partitionDerivative}
    zPositive erbBelow partitionExact scalarMargin =
  let
    coefficientMargin :
      (erbUpper + tail) + vacuumCoefficient < 0ℚ
    coefficientMargin =
      let
        shifted :
          (erbUpper + tail) + vacuumCoefficient
          < (- vacuumCoefficient) + vacuumCoefficient
        shifted = ℚP.+-mono-<-≤ scalarMargin ℚP.≤-refl
      in
      subst
        (λ right → (erbUpper + tail) + vacuumCoefficient < right)
        (Ring.solve-∀ vacuumCoefficient)
        shifted

    scaledMargin :
      ((erbUpper + tail) + vacuumCoefficient) * z < 0ℚ
    scaledMargin =
      let
        instance
          zPositiveI : Positive z
          zPositiveI = positive zPositive
      in
      subst
        (λ right → ((erbUpper + tail) + vacuumCoefficient) * z < right)
        (Ring.solve-∀ z)
        (ℚP.*-monoʳ-<-pos z coefficientMargin)

    actualBelowScaled :
      (erbNumerator + tail * z) + vacuumCoefficient * z
      ≤
      ((erbUpper + tail) + vacuumCoefficient) * z
    actualBelowScaled =
      subst₂ _≤_
        (Ring.solve-∀ erbNumerator tail z vacuumCoefficient)
        (Ring.solve-∀ erbUpper tail vacuumCoefficient z)
        (ℚP.+-mono-≤
          (ℚP.+-mono-≤ erbBelow ℚP.≤-refl)
          ℚP.≤-refl)

    actualNegative :
      (erbNumerator + tail * z) + vacuumCoefficient * z < 0ℚ
    actualNegative = ℚP.≤-<-trans actualBelowScaled scaledMargin

    tailBelowNegativeSource :
      tail * z < - (erbNumerator + vacuumCoefficient * z)
    tailBelowNegativeSource =
      let
        shifted :
          tail * z + (erbNumerator + vacuumCoefficient * z) < 0ℚ
        shifted =
          subst
            (λ left → left < 0ℚ)
            (Ring.solve-∀ erbNumerator tail z vacuumCoefficient)
            actualNegative
      in
      subst
        (λ right → tail * z < right)
        (Ring.solve-∀ erbNumerator vacuumCoefficient z)
        shifted
  in
  subst
    (λ right → tail * z < right)
    partitionExact
    tailBelowNegativeSource

partitionNormalizationValueNotNeededForCoefficientMargin : Bool
partitionNormalizationValueNotNeededForCoefficientMargin = true

preferredB2CanBePaidByERBPlusTailBelowNegativeVacuumCoefficient : Bool
preferredB2CanBePaidByERBPlusTailBelowNegativeVacuumCoefficient = true
