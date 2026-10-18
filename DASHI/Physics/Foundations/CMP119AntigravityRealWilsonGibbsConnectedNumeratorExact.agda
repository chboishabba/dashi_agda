{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealWilsonGibbsConnectedNumeratorExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; _*ℝ_; _-ℝ_)

import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite

------------------------------------------------------------------------
-- CANONICAL UNNORMALIZED WILSON/GIBBS CONNECTED NUMERATOR
--
-- For one literal real finite measure μ and observables F,G:
--
--   N_F  = ∫ ρ F dH
--   N_G  = ∫ ρ G dH
--   N_FG = ∫ ρ FG dH
--   Z    = ∫ ρ dH
--
-- and the raw connected numerator is
--
--   C(F,G) = N_FG Z - N_F N_G.
--
-- This is intentionally NOT identified definitionally with the normalized
-- covariance <FG>-<F><G>.  Such an identification requires the multiplicative
-- quotient laws for the selected real division authority.
------------------------------------------------------------------------

productObservable :
  ∀ {Configuration} →
  (Configuration → ℝ) →
  (Configuration → ℝ) →
  Configuration → ℝ
productObservable left right configuration =
  left configuration *ℝ right configuration

canonicalWilsonGibbsConnectedNumerator :
  ∀ {Configuration} →
  Physical.PhysicalFiniteYMMeasure Configuration ℝ →
  (Configuration → ℝ) →
  (Configuration → ℝ) →
  ℝ
canonicalWilsonGibbsConnectedNumerator measure left right =
  Finite.unnormalizedNumerator measure
      (productObservable left right)
    *ℝ Physical.partitionFunction measure
  -ℝ
  Finite.unnormalizedNumerator measure left
    *ℝ Finite.unnormalizedNumerator measure right

record SelectedCMP119RealConnectedNumeratorWeld
    {Configuration : Set}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ)
    (left right : Configuration → ℝ) : Set₁ where
  field
    selectedCMP119ConnectedNumerator : ℝ

    selectedIsCanonicalWilsonGibbsConnectedNumerator :
      selectedCMP119ConnectedNumerator
      ≡
      canonicalWilsonGibbsConnectedNumerator
        measure left right

open SelectedCMP119RealConnectedNumeratorWeld public

selectedCMP119ConnectedNumeratorIsCanonical :
  ∀ {Configuration measure left right}
    (weld :
      SelectedCMP119RealConnectedNumeratorWeld
        {Configuration = Configuration}
        measure left right) →
  selectedCMP119ConnectedNumerator weld
  ≡
  canonicalWilsonGibbsConnectedNumerator
    measure left right
selectedCMP119ConnectedNumeratorIsCanonical =
  selectedIsCanonicalWilsonGibbsConnectedNumerator

normalizedCovarianceDefinitionallyEqualsRawNumerator : Bool
normalizedCovarianceDefinitionallyEqualsRawNumerator = false

normalizedCovarianceDefinitionallyEqualsRawNumeratorIsFalse :
  normalizedCovarianceDefinitionallyEqualsRawNumerator ≡ false
normalizedCovarianceDefinitionallyEqualsRawNumeratorIsFalse = refl
