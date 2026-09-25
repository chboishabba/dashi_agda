{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119GibbsDiagonalTraceCancellationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _-_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Foundations.CMP119PhysicalFiniteMeasureNZDNDZExact as NZ
import DASHI.Physics.Foundations.CMP119GibbsFiniteMeasureNZDNDZReductionExact as Gibbs
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureIntegrationLawsExact as Integral
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- FOUR-DIAGONAL GIBBS CANCELLATION
--
-- If the classical d=4 metric-action variations obey
--
--   DS00 + DS11 + DS22 + DS33 = 0
--
-- pointwise, then the density-variation contribution cancels from the active
-- connected numerator.  What survives is only the trace of the insertion
-- variation:
--
--   C00 + C11 + C22 + C33
--     = Z * ∫ rho (DO00 + DO11 + DO22 + DO33).
------------------------------------------------------------------------

record FourDiagonalPerturbations (MetricPerturbation : Set) : Set where
  field
    h00 h11 h22 h33 : MetricPerturbation

open FourDiagonalPerturbations public

module _
    {Configuration MetricPerturbation : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (dataSet :
      Gibbs.GibbsMetricInsertionData
        Configuration MetricPerturbation measure)
    (directions : FourDiagonalPerturbations MetricPerturbation)
    (laws : Integral.RationalFiniteMeasureIntegrationLaws measure)
    (actionTraceZero :
      ∀ configuration →
      Gibbs.actionVariation dataSet (h00 directions) configuration
      + Gibbs.actionVariation dataSet (h11 directions) configuration
      + Gibbs.actionVariation dataSet (h22 directions) configuration
      + Gibbs.actionVariation dataSet (h33 directions) configuration
      ≡ 0ℚ)
  where

  stressData =
    Gibbs.asPhysicalMetricStressData dataSet

  traceInsertionVariation : Configuration → ℚ
  traceInsertionVariation configuration =
    Gibbs.insertionVariation dataSet (h00 directions) configuration
    + Gibbs.insertionVariation dataSet (h11 directions) configuration
    + Gibbs.insertionVariation dataSet (h22 directions) configuration
    + Gibbs.insertionVariation dataSet (h33 directions) configuration

  traceInsertionNumerator : ℚ
  traceInsertionNumerator =
    Physical.haarIntegral measure
      (λ configuration →
        Physical.density measure configuration
        * traceInsertionVariation configuration)

  d00 d11 d22 d33 : ℚ
  d00 = NZ.denominatorDerivative stressData (h00 directions)
  d11 = NZ.denominatorDerivative stressData (h11 directions)
  d22 = NZ.denominatorDerivative stressData (h22 directions)
  d33 = NZ.denominatorDerivative stressData (h33 directions)

  b00 b11 b22 b33 : ℚ
  b00 = NZ.numeratorDerivative stressData (h00 directions)
  b11 = NZ.numeratorDerivative stressData (h11 directions)
  b22 = NZ.numeratorDerivative stressData (h22 directions)
  b33 = NZ.numeratorDerivative stressData (h33 directions)

  c00 c11 c22 c33 : ℚ
  c00 = NZ.connectedCrossNumerator stressData (h00 directions)
  c11 = NZ.connectedCrossNumerator stressData (h11 directions)
  c22 = NZ.connectedCrossNumerator stressData (h22 directions)
  c33 = NZ.connectedCrossNumerator stressData (h33 directions)

  densityDerivativeTraceZero :
    ∀ configuration →
    Gibbs.gibbsDensityDerivative dataSet (h00 directions) configuration
    + Gibbs.gibbsDensityDerivative dataSet (h11 directions) configuration
    + Gibbs.gibbsDensityDerivative dataSet (h22 directions) configuration
    + Gibbs.gibbsDensityDerivative dataSet (h33 directions) configuration
    ≡ 0ℚ
  densityDerivativeTraceZero configuration
    rewrite actionTraceZero configuration =
    ℚRing.solve-∀ (Physical.density measure configuration)

  denominatorDerivativeTraceZero :
    d00 + d11 + d22 + d33 ≡ 0ℚ
  denominatorDerivativeTraceZero =
    let
      f00 = Gibbs.gibbsDensityDerivative dataSet (h00 directions)
      f11 = Gibbs.gibbsDensityDerivative dataSet (h11 directions)
      f22 = Gibbs.gibbsDensityDerivative dataSet (h22 directions)
      f33 = Gibbs.gibbsDensityDerivative dataSet (h33 directions)

      integralSum :
        Physical.haarIntegral measure
          (λ configuration →
            (f00 configuration + f11 configuration)
            + (f22 configuration + f33 configuration))
        ≡
        (Physical.haarIntegral measure f00
          + Physical.haarIntegral measure f11)
        +
        (Physical.haarIntegral measure f22
          + Physical.haarIntegral measure f33)
      integralSum =
        Integral.haarIntegralFourAdd laws f00 f11 f22 f33

      sumIntegrandZero :
        Physical.haarIntegral measure
          (λ configuration →
            (f00 configuration + f11 configuration)
            + (f22 configuration + f33 configuration))
        ≡
        Physical.haarIntegral measure (λ _ → 0ℚ)
      sumIntegrandZero =
        Integral.haarIntegralCongruent laws _ _
          (λ configuration →
            trans
              (ℚRing.solve-∀
                (f00 configuration) (f11 configuration)
                (f22 configuration) (f33 configuration))
              (densityDerivativeTraceZero configuration))
    in
    trans
      (ℚRing.solve-∀
        (Physical.haarIntegral measure f00)
        (Physical.haarIntegral measure f11)
        (Physical.haarIntegral measure f22)
        (Physical.haarIntegral measure f33))
      (trans
        (sym integralSum)
        (trans sumIntegrandZero (Integral.haarIntegralZero laws)))

  numeratorDerivativeTrace :
    b00 + b11 + b22 + b33 ≡ traceInsertionNumerator
  numeratorDerivativeTrace =
    let
      g00 = Gibbs.gibbsNumeratorDerivativeIntegrand dataSet (h00 directions)
      g11 = Gibbs.gibbsNumeratorDerivativeIntegrand dataSet (h11 directions)
      g22 = Gibbs.gibbsNumeratorDerivativeIntegrand dataSet (h22 directions)
      g33 = Gibbs.gibbsNumeratorDerivativeIntegrand dataSet (h33 directions)

      integralSum =
        Integral.haarIntegralFourAdd laws g00 g11 g22 g33

      pointwiseCollapse :
        ∀ configuration →
        (g00 configuration + g11 configuration)
        + (g22 configuration + g33 configuration)
        ≡
        Physical.density measure configuration
        * traceInsertionVariation configuration
      pointwiseCollapse configuration
        rewrite actionTraceZero configuration =
        ℚRing.solve-∀
          (Physical.density measure configuration)
          (Gibbs.insertionObservable dataSet configuration)
          (Gibbs.insertionVariation dataSet (h00 directions) configuration)
          (Gibbs.insertionVariation dataSet (h11 directions) configuration)
          (Gibbs.insertionVariation dataSet (h22 directions) configuration)
          (Gibbs.insertionVariation dataSet (h33 directions) configuration)
          (Gibbs.actionVariation dataSet (h00 directions) configuration)
          (Gibbs.actionVariation dataSet (h11 directions) configuration)
          (Gibbs.actionVariation dataSet (h22 directions) configuration)
          (Gibbs.actionVariation dataSet (h33 directions) configuration)
    in
    trans
      (ℚRing.solve-∀
        (Physical.haarIntegral measure g00)
        (Physical.haarIntegral measure g11)
        (Physical.haarIntegral measure g22)
        (Physical.haarIntegral measure g33))
      (trans
        (sym integralSum)
        (Integral.haarIntegralCongruent laws _ _ pointwiseCollapse))

  activeConnectedNumerator : ℚ
  activeConnectedNumerator = c00 + c11 + c22 + c33

  activeConnectedNumeratorIsPartitionTimesTraceInsertion :
    activeConnectedNumerator
    ≡ Physical.partitionFunction measure * traceInsertionNumerator
  activeConnectedNumeratorIsPartitionTimesTraceInsertion
    rewrite denominatorDerivativeTraceZero
          | numeratorDerivativeTrace =
    ℚRing.solve-∀
      (NZ.numerator stressData)
      (Physical.partitionFunction measure)
      traceInsertionNumerator
