module DASHI.Analysis.BishopFirstOrderRateDiscreteContractionExact where

------------------------------------------------------------------------
-- POSITIVE CONTINUOUS FIRST-ORDER RATE -> DISCRETE BISHOP CONTRACTION
--
-- DASHI CONTRIBUTION
--
-- For a positive first-order rate k and positive discrete time step Δt,
--
--   x = k Δt > 0
--   r = exp(-x)
--
-- and therefore, by the imported global negative-exponential theorem,
--
--   0 < r < 1.
--
-- This is application-neutral mathematics.  A source may own an empirical
-- first-order rate and time unit; it does not thereby own this discretisation
-- theorem, nor does this theorem authorize extrapolation beyond the source's
-- fitted/observed time window.
------------------------------------------------------------------------

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as NegExp

record PositiveFirstOrderDiscretisation : Set where
  field
    rate : BishopReal.ℝ
    timeStep : BishopReal.ℝ

    ratePositive :
      BishopReal._<_ BishopReal.0ℝ rate

    timeStepPositive :
      BishopReal._<_ BishopReal.0ℝ timeStep

open PositiveFirstOrderDiscretisation public

rateTimesStep :
  PositiveFirstOrderDiscretisation →
  BishopReal.ℝ
rateTimesStep inputs =
  BishopReal._*_
    (rate inputs)
    (timeStep inputs)

rateTimesStepPositive :
  (inputs : PositiveFirstOrderDiscretisation) →
  BishopReal._<_
    BishopReal.0ℝ
    (rateTimesStep inputs)
rateTimesStepPositive inputs =
  BishopP.posx⇒0<x
    (BishopP.posx,y⇒posx*y
      (BishopP.0<x⇒posx (ratePositive inputs))
      (BishopP.0<x⇒posx (timeStepPositive inputs)))

discreteContractionRatio :
  PositiveFirstOrderDiscretisation →
  BishopReal.ℝ
discreteContractionRatio inputs =
  Exp.bishopExp
    (BishopReal.- (rateTimesStep inputs))

discreteContractionRatioPositive :
  (inputs : PositiveFirstOrderDiscretisation) →
  BishopReal._<_
    BishopReal.0ℝ
    (discreteContractionRatio inputs)
discreteContractionRatioPositive inputs =
  NegExp.negativeExpPositive
    (rateTimesStepPositive inputs)

discreteContractionRatioBelowOne :
  (inputs : PositiveFirstOrderDiscretisation) →
  BishopReal._<_
    (discreteContractionRatio inputs)
    BishopReal.1ℝ
discreteContractionRatioBelowOne inputs =
  NegExp.negativeExpBelowOne
    (rateTimesStepPositive inputs)
