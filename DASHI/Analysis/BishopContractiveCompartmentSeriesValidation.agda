module DASHI.Analysis.BishopContractiveCompartmentSeriesValidation where

open import Agda.Builtin.Nat using (Nat)

import Real as BishopReal
import Sequence as BishopSequence

import DASHI.Analysis.BishopContractiveCompartmentSeriesExact as P
import DASHI.Analysis.BishopFirstOrderRateDiscreteContractionExact as FirstOrder

majorantAbsoluteConvergenceRegression :
  (problem : P.BishopPolynomialGeometricCompartment) →
  BishopSequence.SeriesOf_ConvergesAbsolutely
    (P.compartmentMajorantTerm problem)
majorantAbsoluteConvergenceRegression =
  P.compartmentMajorantAbsolutelyConvergent

majorantConvergenceRegression :
  (problem : P.BishopPolynomialGeometricCompartment) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf
      (P.compartmentMajorantTerm problem))
majorantConvergenceRegression =
  P.compartmentMajorantConvergent


dominatedSeriesConvergenceRegression :
  (problem : P.BishopDominatedCompartmentSeries) →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf
      (P.actualContribution problem))
dominatedSeriesConvergenceRegression =
  P.dominatedCompartmentSeriesConvergent

dominatedPartialSumsCauchyRegression :
  (problem : P.BishopDominatedCompartmentSeries) →
  BishopSequence._isCauchy
    (BishopSequence.SeriesOf
      (P.actualContribution problem))
dominatedPartialSumsCauchyRegression =
  P.dominatedCompartmentPartialSumsCauchy


firstOrderCompartmentRatioPositiveRegression :
  (inputs : FirstOrder.PositiveFirstOrderDiscretisation) →
  (scale : BishopReal.ℝ) →
  (degree : Nat) →
  (scaleNN : BishopReal.NonNegative scale) →
  BishopReal._<_
    BishopReal.0ℝ
    (P.ratio
      (P.firstOrderPolynomialGeometricCompartment
        inputs scale degree scaleNN))
firstOrderCompartmentRatioPositiveRegression inputs scale degree scaleNN =
  FirstOrder.discreteContractionRatioPositive inputs

firstOrderCompartmentRatioBelowOneRegression :
  (inputs : FirstOrder.PositiveFirstOrderDiscretisation) →
  (scale : BishopReal.ℝ) →
  (degree : Nat) →
  (scaleNN : BishopReal.NonNegative scale) →
  BishopReal._<_
    (P.ratio
      (P.firstOrderPolynomialGeometricCompartment
        inputs scale degree scaleNN))
    BishopReal.1ℝ
firstOrderCompartmentRatioBelowOneRegression inputs scale degree scaleNN =
  P.ratioBelowOne
    (P.firstOrderPolynomialGeometricCompartment
      inputs scale degree scaleNN)
