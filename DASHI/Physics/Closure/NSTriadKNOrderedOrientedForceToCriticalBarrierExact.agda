module DASHI.Physics.Closure.NSTriadKNOrderedOrientedForceToCriticalBarrierExact where

------------------------------------------------------------------------
-- CANONICAL PERIODIC-B ANALYTIC ENDGAME
--
-- This owner removes route-specific intermediate obligations from the
-- mandatory Clay-B path.
--
-- Existing exact same-object chain:
--
--   2 * integratedOrderedOrientedForce
--     <= cutoffIndependentBound
--   -> R503 DirectOffDiagonalBudget
--   -> R415 IntegratedSignedHeatCrossPayment
--   -> R410 literal-R406 cancellation
--   + same-object R414 critical slice
--   + cutoff-uniform initial-critical realization
--   -> Round104 UniformSignedCriticalProductionFamily
--   -> cutoff-uniform critical barrier.
--
-- No four-sign Gram residual, Schur majorization, forcing norm-square,
-- amplitude-side independent budget, or second remainder estimate is required
-- by this route.
--
-- This file is a compiler only.  It does not manufacture the two genuinely
-- analytic inputs:
--
--   * the cutoff-uniform signed ordered-oriented spacetime budget;
--   * the phase-sensitive literal-R406 critical-production slice (including
--     positive retained viscosity) and its cutoff-uniform initial ceiling.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact as R503
import DASHI.Physics.Closure.NSTriadKNOrderedOrientedForceToR503BidiExact as Ordered
import DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact as R414
import DASHI.Physics.Closure.NSTriadKNSignedHeatCrossDirectToCriticalBarrierRound421Exact as R421
import DASHI.Physics.Closure.NSTriadKNInitialCriticalRealizationToR421Round512Exact as R512
import DASHI.Physics.Closure.NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact as Signed
import DASHI.Physics.Closure.NSTriadKNSignedHeatCrossToR410Round415Exact as R415

F : C3.RealField _
F = Rational.rationalRealField

module CanonicalCriticalEndgame
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module OrderedToR503 = Ordered.OrderedToR503
    Time initialTime integrateTo DerivativeOf integration
  module Direct = R503.DirectSignedCross
    Time initialTime integrateTo DerivativeOf integration
  module Unified = R414.Unified
    Time initialTime integrateTo DerivativeOf
  module Barrier = R421.DirectBarrier
    Time initialTime integrateTo DerivativeOf
  module Initial = R512.InitialCritical
    Time initialTime integrateTo DerivativeOf
  module Heat = R415.SignedHeatCross
    Time initialTime integrateTo DerivativeOf

  record CanonicalCriticalEndgameInputs
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (terminal : Time) : Set₁ where
    field
      signedOrderedBudget :
        OrderedToR503.OrderedOrientedSpacetimeBudget T R

      literalCriticalSlice :
        (cutoff : Nat) →
        Unified.CriticalSliceOnLiteralR406 T R terminal cutoff

      initialCriticalRealization :
        Initial.InitialCriticalRealization
          T R terminal literalCriticalSlice

  open CanonicalCriticalEndgameInputs public

  signedOrderedBudgetBuildsR503 :
    ∀ {T R terminal} →
    CanonicalCriticalEndgameInputs T R terminal →
    Direct.DirectOffDiagonalBudget T R
  signedOrderedBudgetBuildsR503 I =
    OrderedToR503.orderedBudgetBuildsR503 (signedOrderedBudget I)

  signedOrderedBudgetBuildsR415 :
    ∀ {T R terminal} →
    CanonicalCriticalEndgameInputs T R terminal →
    Heat.IntegratedSignedHeatCrossPayment T R
  signedOrderedBudgetBuildsR415 I =
    Direct.directBudgetBuildsR415 (signedOrderedBudgetBuildsR503 I)

  canonicalR421Data :
    ∀ {T R terminal} →
    (I : CanonicalCriticalEndgameInputs T R terminal) →
    Barrier.SignedHeatCriticalData T R terminal
  canonicalR421Data I =
    Initial.attachInitialCriticalRealization
      (signedOrderedBudgetBuildsR415 I)
      (literalCriticalSlice I)
      (initialCriticalRealization I)

  canonicalUniformSignedCriticalFamily :
    ∀ {T R terminal} →
    CanonicalCriticalEndgameInputs T R terminal →
    Signed.UniformSignedCriticalProductionFamily
  canonicalUniformSignedCriticalFamily I =
    Barrier.signedHeatCrossBuildsUniformCriticalFamily
      (canonicalR421Data I)

  canonicalUniformCriticalBarrier :
    ∀ {T R terminal} →
    (I : CanonicalCriticalEndgameInputs T R terminal) →
    (cutoff : Nat) →
    let family = canonicalUniformSignedCriticalFamily I in
    Signed.terminalCritical (Signed.slice family cutoff)
      + Signed.retainedViscosity (Signed.slice family cutoff)
          * Signed.criticalDissipation (Signed.slice family cutoff)
    ≤ Signed.uniformCriticalCeiling family
  canonicalUniformCriticalBarrier I cutoff =
    Barrier.signedHeatCrossBuildsUniformCriticalBarrier
      (canonicalR421Data I)
      cutoff
