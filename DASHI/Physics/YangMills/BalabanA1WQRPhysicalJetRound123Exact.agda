{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA1WQRPhysicalJetRound123Exact where

------------------------------------------------------------------------
-- ROUND123 A1: ACTUAL W/Q/R -> GAUSSIAN JET -> FIVE CHANNELS -> (5.42)
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _+_; -_)
import Data.Nat.Base as ℕ

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA1FiveChannelEvaluatorBidiRound117Exact as A1
import DASHI.Physics.YangMills.BalabanA1HistoryUniformTwoSidedBetaRound102Exact as Cert
import DASHI.Physics.YangMills.BalabanCMP109GaussianFirstVariationSourceDecompositionExact as WQR

record A1WQRPhysicalJetInputs (History Cell : Set) : Set₁ where
  field
    reduced : A1.A1ReducedSameObjectInputs History Cell

    Background Variation Operator ConstrainedOperator : Set
    Momentum Lorentz Color : Set

    gaussianCalculation : ∀ K k → k ℕ.< K →
      WQR.CMP109GaussianFirstVariationCalculation
        Background Variation Operator ConstrainedOperator
        Momentum Lorentz Color ℚ

    -- Actual mixed p_mu p_nu coefficient extractor used at p=0.  It acts on
    -- the full momentum/Lorentz/color source symbol, so the three displayed
    -- channel scalars below are not free convention labels.
    mixedMomentumCoefficient :
      (Momentum → Lorentz → Lorentz → Lorentz → Color → Color → Color → ℚ) → ℚ

    wilsonMixedCoefficient : ∀ K k (k<K : k ℕ.< K) → ℚ
    averagingMixedCoefficient : ∀ K k (k<K : k ℕ.< K) → ℚ
    gaugeMixedCoefficient : ∀ K k (k<K : k ℕ.< K) → ℚ

    wilsonMixedCoefficientExact : ∀ K k (k<K : k ℕ.< K) →
      wilsonMixedCoefficient K k k<K
      ≡ mixedMomentumCoefficient
          (WQR.wilsonFirstVariationSymbol (gaussianCalculation K k k<K))

    averagingMixedCoefficientExact : ∀ K k (k<K : k ℕ.< K) →
      averagingMixedCoefficient K k k<K
      ≡ mixedMomentumCoefficient
          (WQR.averagingFirstVariationSymbol (gaussianCalculation K k k<K))

    gaugeMixedCoefficientExact : ∀ K k (k<K : k ℕ.< K) →
      gaugeMixedCoefficient K k k<K
      ≡ mixedMomentumCoefficient
          (WQR.gaugeProjectionFirstVariationSymbol (gaussianCalculation K k k<K))

    -- Genuine source calculation: the Gaussian coefficient of the SAME
    -- history/jet is the negative p=0 mixed coefficient of W+Q+R.
    gaussianBetaIsWQR : ∀ K k (k<K : k ℕ.< K) →
      Cert.betaZ (A1.certificate reduced)
          (A1.historyForShell reduced K k k<K)
      ≡ - (wilsonMixedCoefficient K k k<K
          + (averagingMixedCoefficient K k k<K
            + gaugeMixedCoefficient K k k<K))

open A1WQRPhysicalJetInputs public

asReducedA1Inputs :
  ∀ {History Cell} →
  A1WQRPhysicalJetInputs History Cell →
  A1.A1ReducedSameObjectInputs History Cell
asReducedA1Inputs = reduced

a1WQRGaussianCoefficientExact :
  ∀ {History Cell}
    (dataSet : A1WQRPhysicalJetInputs History Cell)
    K k (k<K : k ℕ.< K) →
  Cert.betaZ (A1.certificate (reduced dataSet))
      (A1.historyForShell (reduced dataSet) K k k<K)
  ≡ - (wilsonMixedCoefficient dataSet K k k<K
      + (averagingMixedCoefficient dataSet K k k<K
        + gaugeMixedCoefficient dataSet K k k<K))
a1WQRGaussianCoefficientExact = gaussianBetaIsWQR

a1WQRPhysicalJetPackagingLevel : ProofLevel
a1WQRPhysicalJetPackagingLevel = machineChecked

-- Exact remaining source calculation for A1: instantiate the literal
-- CMP99/CMP98/CMP109 symbols and prove their p=0 mixed coefficients sum to the
-- Gaussian coefficient of the same generated Eq.(5.1) jet.  No opaque symbol
-- receipt remains in this bundle.
literalA1WQRMixedCoefficientCalculationLevel : ProofLevel
literalA1WQRMixedCoefficientCalculationLevel = conditional
