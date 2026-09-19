module DASHI.Moonshine.JInvariantBishopUpperHalfPlaneEisensteinFromUnitPhaseExact where

------------------------------------------------------------------------
-- UPPER-HALF-PLANE BISHOP E4/E6 FROM A UNIT PHASE
--
-- DASHI CONTRIBUTION
--
-- This is the preferred setoid-native convergence endpoint.
--
-- Given:
--
--   * pi_B > 0;
--   * Im_B(tau) > 0;
--   * one Bishop complex phase with normSq ~= 1;
--   * the generic nonnegative square-order reflection capability;
--
-- the already-owned global negative-exponential theorem constructs
--
--   r = exp_B(-(2*pi_B*Im_B(tau))) in [0,1),
--
-- the radius × unit-phase compiler constructs a Bishop q with the required
-- all-power component envelope, and the setoid Eisenstein owner produces
-- canonical constructive E4/E6 q-series limits.
--
-- No legacy ConcreteComplex quotient, principal branch, or ordinary modulus
-- package enters this endpoint.
------------------------------------------------------------------------

import Real as BishopReal

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopQFromUnitPhaseExact as Q

e4UpperHalfPlaneLimitFromUnitPhase :
  ∀ (phase : Complex.BishopComplex)
    {piB imagB : BishopReal.ℝ}
    (phaseUnit : BishopReal._≃_ (Norm.normSqC phase) BishopReal.1ℝ)
    (piPositive : BishopReal._<_ BishopReal.0ℝ piB)
    (imagPositive : BishopReal._<_ BishopReal.0ℝ imagB)
    (reflection : Norm.BishopNonnegativeSquareReflection) →
  Complex.BishopComplex
e4UpperHalfPlaneLimitFromUnitPhase
  phase {piB} {imagB} phaseUnit piPositive imagPositive reflection =
  Q.e4LimitFromUnitPhase
    phase
    phaseUnit
    (Radius.qRadiusUnitInterval piPositive imagPositive)
    reflection

e6UpperHalfPlaneLimitFromUnitPhase :
  ∀ (phase : Complex.BishopComplex)
    {piB imagB : BishopReal.ℝ}
    (phaseUnit : BishopReal._≃_ (Norm.normSqC phase) BishopReal.1ℝ)
    (piPositive : BishopReal._<_ BishopReal.0ℝ piB)
    (imagPositive : BishopReal._<_ BishopReal.0ℝ imagB)
    (reflection : Norm.BishopNonnegativeSquareReflection) →
  Complex.BishopComplex
e6UpperHalfPlaneLimitFromUnitPhase
  phase {piB} {imagB} phaseUnit piPositive imagPositive reflection =
  Q.e6LimitFromUnitPhase
    phase
    phaseUnit
    (Radius.qRadiusUnitInterval piPositive imagPositive)
    reflection
