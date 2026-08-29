{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA1WQRPhysicalJetRound123Exact where

------------------------------------------------------------------------
-- ROUND123 A1: ACTUAL W/Q/R -> GAUSSIAN JET -> FIVE CHANNELS -> (5.42)
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _+_; -_)
import Data.Nat.Base as ℕ
open import Relation.Binary.PropositionalEquality using (cong; trans)

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

    -- Actual p_mu p_nu coefficient extractor at p=0.
    mixedMomentumCoefficient :
      (Momentum → Lorentz → Lorentz → Lorentz → Color → Color → Color → ℚ) → ℚ

    -- The extractor is extensional and linear over the literal scalar addition
    -- carried by each source calculation.  These are ordinary properties of a
    -- mixed derivative/coefficient map, separated from the physical W/Q/R
    -- evaluation itself.
    mixedCoefficientExtensional :
      ∀ f g →
      (∀ momentum output input backgroundDirection
          outputColor inputColor backgroundColor →
        f momentum output input backgroundDirection
          outputColor inputColor backgroundColor
        ≡ g momentum output input backgroundDirection
          outputColor inputColor backgroundColor) →
      mixedMomentumCoefficient f ≡ mixedMomentumCoefficient g

    mixedCoefficientAdditive :
      ∀ K k (k<K : k ℕ.< K) f g →
      mixedMomentumCoefficient
        (λ momentum output input backgroundDirection
            outputColor inputColor backgroundColor →
          WQR.add (gaussianCalculation K k k<K)
            (f momentum output input backgroundDirection
              outputColor inputColor backgroundColor)
            (g momentum output input backgroundDirection
              outputColor inputColor backgroundColor))
      ≡ mixedMomentumCoefficient f + mixedMomentumCoefficient g

    -- The genuinely physical Eq.(5.1) Gaussian calculation: betaZ is the
    -- negative mixed coefficient of the SAME constrained Gaussian symbol.
    gaussianBetaIsNegativeConstrainedMixed :
      ∀ K k (k<K : k ℕ.< K) →
      Cert.betaZ (A1.certificate reduced)
          (A1.historyForShell reduced K k k<K)
      ≡ - mixedMomentumCoefficient
          (WQR.literalConstrainedFirstVariationSymbol
            (gaussianCalculation K k k<K))

open A1WQRPhysicalJetInputs public

asReducedA1Inputs :
  ∀ {History Cell} →
  A1WQRPhysicalJetInputs History Cell →
  A1.A1ReducedSameObjectInputs History Cell
asReducedA1Inputs = reduced

wilsonMixedCoefficient :
  ∀ {History Cell} → A1WQRPhysicalJetInputs History Cell →
  ∀ K k → k ℕ.< K → ℚ
wilsonMixedCoefficient dataSet K k k<K =
  mixedMomentumCoefficient dataSet
    (WQR.wilsonFirstVariationSymbol
      (gaussianCalculation dataSet K k k<K))

averagingMixedCoefficient :
  ∀ {History Cell} → A1WQRPhysicalJetInputs History Cell →
  ∀ K k → k ℕ.< K → ℚ
averagingMixedCoefficient dataSet K k k<K =
  mixedMomentumCoefficient dataSet
    (WQR.averagingFirstVariationSymbol
      (gaussianCalculation dataSet K k k<K))

gaugeMixedCoefficient :
  ∀ {History Cell} → A1WQRPhysicalJetInputs History Cell →
  ∀ K k → k ℕ.< K → ℚ
gaugeMixedCoefficient dataSet K k k<K =
  mixedMomentumCoefficient dataSet
    (WQR.gaugeProjectionFirstVariationSymbol
      (gaussianCalculation dataSet K k k<K))

constrainedMixedCoefficientIsWQR :
  ∀ {History Cell}
    (dataSet : A1WQRPhysicalJetInputs History Cell)
    K k (k<K : k ℕ.< K) →
  mixedMomentumCoefficient dataSet
      (WQR.literalConstrainedFirstVariationSymbol
        (gaussianCalculation dataSet K k k<K))
  ≡ wilsonMixedCoefficient dataSet K k k<K
      + (averagingMixedCoefficient dataSet K k k<K
        + gaugeMixedCoefficient dataSet K k k<K)
constrainedMixedCoefficientIsWQR dataSet K k k<K =
  let
    calc = gaussianCalculation dataSet K k k<K
    W = WQR.wilsonFirstVariationSymbol calc
    Q = WQR.averagingFirstVariationSymbol calc
    R = WQR.gaugeProjectionFirstVariationSymbol calc
    QR = λ momentum output input backgroundDirection outputColor inputColor backgroundColor →
      WQR.add calc
        (Q momentum output input backgroundDirection outputColor inputColor backgroundColor)
        (R momentum output input backgroundDirection outputColor inputColor backgroundColor)
    WQRsum = λ momentum output input backgroundDirection outputColor inputColor backgroundColor →
      WQR.add calc
        (W momentum output input backgroundDirection outputColor inputColor backgroundColor)
        (QR momentum output input backgroundDirection outputColor inputColor backgroundColor)

    pointwise : ∀ momentum output input backgroundDirection outputColor inputColor backgroundColor →
      WQR.literalConstrainedFirstVariationSymbol calc
        momentum output input backgroundDirection outputColor inputColor backgroundColor
      ≡ WQRsum
        momentum output input backgroundDirection outputColor inputColor backgroundColor
    pointwise = WQR.WQRAssemblyExact calc

    ext = mixedCoefficientExtensional dataSet
      (WQR.literalConstrainedFirstVariationSymbol calc) WQRsum pointwise

    outer = mixedCoefficientAdditive dataSet K k k<K W QR
    inner = mixedCoefficientAdditive dataSet K k k<K Q R
  in
  trans ext
    (trans outer
      (cong
        (λ right → mixedMomentumCoefficient dataSet W + right)
        inner))

a1WQRGaussianCoefficientExact :
  ∀ {History Cell}
    (dataSet : A1WQRPhysicalJetInputs History Cell)
    K k (k<K : k ℕ.< K) →
  Cert.betaZ (A1.certificate (reduced dataSet))
      (A1.historyForShell (reduced dataSet) K k k<K)
  ≡ - (wilsonMixedCoefficient dataSet K k k<K
      + (averagingMixedCoefficient dataSet K k k<K
        + gaugeMixedCoefficient dataSet K k k<K))
a1WQRGaussianCoefficientExact dataSet K k k<K =
  trans
    (gaussianBetaIsNegativeConstrainedMixed dataSet K k k<K)
    (cong -_ (constrainedMixedCoefficientIsWQR dataSet K k k<K))

a1WQRPointwiseToMixedCoefficientLevel : ProofLevel
a1WQRPointwiseToMixedCoefficientLevel = machineChecked

a1WQRPhysicalJetPackagingLevel : ProofLevel
a1WQRPhysicalJetPackagingLevel = machineChecked

-- Remaining A1 source calculation is now exactly one equality:
-- betaZ equals the negative mixed coefficient of the literal constrained
-- Eq.(5.1) Gaussian symbol.  W/Q/R splitting of that coefficient is downstream
-- from the pointwise source assembly and linearity above.
literalA1ConstrainedGaussianMixedCoefficientLevel : ProofLevel
literalA1ConstrainedGaussianMixedCoefficientLevel = conditional
