module DASHI.Analysis.BishopFirstOrderRateDiscreteContractionValidation where

import Real as BishopReal
import DASHI.Analysis.BishopFirstOrderRateDiscreteContractionExact as P

positiveRateStepRegression :
  (inputs : P.PositiveFirstOrderDiscretisation) →
  BishopReal._<_
    BishopReal.0ℝ
    (P.rateTimesStep inputs)
positiveRateStepRegression = P.rateTimesStepPositive

ratioPositiveRegression :
  (inputs : P.PositiveFirstOrderDiscretisation) →
  BishopReal._<_
    BishopReal.0ℝ
    (P.discreteContractionRatio inputs)
ratioPositiveRegression = P.discreteContractionRatioPositive

ratioBelowOneRegression :
  (inputs : P.PositiveFirstOrderDiscretisation) →
  BishopReal._<_
    (P.discreteContractionRatio inputs)
    BishopReal.1ℝ
ratioBelowOneRegression = P.discreteContractionRatioBelowOne
