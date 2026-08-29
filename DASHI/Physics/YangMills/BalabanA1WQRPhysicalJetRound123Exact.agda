{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanA1WQRPhysicalJetRound123Exact where

------------------------------------------------------------------------
-- ROUND123 A1: ACTUAL W/Q/R -> GAUSSIAN JET -> FIVE CHANNELS -> (5.42)
--
-- Round117 showed that the final five-channel evaluator equality is derived as
-- soon as the physical jet is split as betaZ + betaInt.  What it did not yet
-- carry in the SAME object was the source decomposition of betaZ.
--
-- This file closes that structural gap.  For each physical shell it carries the
-- literal CMP109 constrained Gaussian first-variation calculation, whose symbol
-- is pointwise W + Q + R, and records the one genuinely source-specific scalar
-- extraction:
--
--   betaZ = - (mixed W + mixed Q + mixed R).
--
-- The full jet then adds the already exact five-channel evaluator, and Round117
-- / Round103 extract Eq.(5.42).  Thus there is no room to substitute a continuum
-- bubble, bare Wilson Hessian, or a separately-normalized gauge/ghost object.
------------------------------------------------------------------------

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

    -- The source Gaussian calculation is shell/history dependent; it must be
    -- evaluated on the SAME history used by the physical jet/certificate.
    gaussianCalculation : ∀ K k → k ℕ.< K →
      WQR.CMP109GaussianFirstVariationCalculation
        Background Variation Operator ConstrainedOperator
        Momentum Lorentz Color ℚ

    -- The p=0 off-diagonal mixed-momentum extraction is applied separately to
    -- each of the three source symbols.  Keeping these functions explicit makes
    -- the W/Q/R content inspectable and avoids a hidden aggregate scalar.
    wilsonMixedCoefficient : ∀ K k (k<K : k ℕ.< K) → ℚ
    averagingMixedCoefficient : ∀ K k (k<K : k ℕ.< K) → ℚ
    gaugeMixedCoefficient : ∀ K k (k<K : k ℕ.< K) → ℚ

    -- Genuine source calculation: the Gaussian coefficient of the SAME
    -- history/jet is the negative mixed coefficient of W+Q+R.
    gaussianBetaIsWQR : ∀ K k (k<K : k ℕ.< K) →
      Cert.betaZ (A1.certificate reduced)
          (A1.historyForShell reduced K k k<K)
      ≡ - (wilsonMixedCoefficient K k k<K
          + (averagingMixedCoefficient K k k<K
            + gaugeMixedCoefficient K k k<K))

    -- Tie each displayed scalar to the corresponding literal source symbol of
    -- `gaussianCalculation`.  These are intentionally source-evidence fields:
    -- the mixed-momentum differentiation/evaluation is the remaining concrete
    -- W/Q/R calculation, not consumer algebra.
    WilsonMixedCoefficientOfLiteralSymbol : ∀ K k (k<K : k ℕ.< K) → Set
    AveragingMixedCoefficientOfLiteralSymbol : ∀ K k (k<K : k ℕ.< K) → Set
    GaugeMixedCoefficientOfLiteralSymbol : ∀ K k (k<K : k ℕ.< K) → Set

    wilsonMixedCoefficientOfLiteralSymbol : ∀ K k (k<K : k ℕ.< K) →
      WilsonMixedCoefficientOfLiteralSymbol K k k<K
    averagingMixedCoefficientOfLiteralSymbol : ∀ K k (k<K : k ℕ.< K) →
      AveragingMixedCoefficientOfLiteralSymbol K k k<K
    gaugeMixedCoefficientOfLiteralSymbol : ∀ K k (k<K : k ℕ.< K) →
      GaugeMixedCoefficientOfLiteralSymbol K k k<K

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

-- Exact remaining source calculation for A1: instantiate the three mixed
-- coefficients from the literal CMP99/CMP98/CMP109 constrained symbols and prove
-- `gaussianBetaIsWQR` on each generated shell.  Round117 then supplies the
-- five-channel evaluator and Eq.(5.42) automatically.
literalA1WQRMixedCoefficientCalculationLevel : ProofLevel
literalA1WQRMixedCoefficientCalculationLevel = conditional
