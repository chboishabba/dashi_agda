module DASHI.Physics.Closure.NSTriadKNSignedRateVectorPaymentToR503Exact where

------------------------------------------------------------------------
-- S2b2d1b2 -> S2b2d2 -> R503 CONDITIONAL COMPILER
--
-- A1 and A2 now expose the literal physical signed family
--
--   sum_{alpha<beta} (r_alpha-r_beta) W(M,A_alpha-A_beta).
--
-- This owner names the missing theorem itself and separates it from the
-- already-existing global ordered-kernel/R503 compiler.  No inhabitant of the
-- analytic payment is manufactured.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as PhysicalField
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentWorkDifferenceVectorBridgeExact as Vector
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateDifferenceExact as Rate
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNOrderedOrientedForceToR503BidiExact as OrderedToR503
import DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact as R503

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- A3: exact local theorem shape.  This is the genuinely new NS payment.
------------------------------------------------------------------------

record FixedOutputSignedRateVectorPayment
    (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F)
    (mixed : C3.Complex3 F)
    (value : Physical.PhysicalTriadIncidence → C3.Complex3 F)
    (items : List Physical.PhysicalTriadIncidence) : Set where
  field
    residualBudget : ℚ
    signedRateVectorPayment :
      0 - Vector.pairDifferenceVectorWorkSum
          (Rate.physicalCellRate system) mixed value items
      ≤ residualBudget

open FixedOutputSignedRateVectorPayment public

------------------------------------------------------------------------
-- A4/A5: the cutoff-uniform global theorem is exactly the already-selected
-- OrderedOrientedSpacetimeBudget; once supplied, R503 is automatic.
------------------------------------------------------------------------

module GlobalCompiler
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Ordered = OrderedToR503.OrderedToR503
    Time initialTime integrateTo DerivativeOf integration
  module Direct = R503.DirectSignedCross
    Time initialTime integrateTo DerivativeOf integration
  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf

  S2b2GlobalSpacetimePayment :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    Support.LiteralNonzeroCutoffTrajectory T → Set₁
  S2b2GlobalSpacetimePayment = Ordered.OrderedOrientedSpacetimeBudget

  s2b2PaymentBuildsDirectOffDiagonalBudget :
    ∀ {T R} →
    S2b2GlobalSpacetimePayment T R →
    Direct.DirectOffDiagonalBudget T R
  s2b2PaymentBuildsDirectOffDiagonalBudget =
    Ordered.orderedBudgetBuildsR503

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

a3ExactSignedRateVectorPaymentTypeConstructed : Bool
a3ExactSignedRateVectorPaymentTypeConstructed = true

a3QuantitativePhysicalPaymentClosed : Bool
a3QuantitativePhysicalPaymentClosed = false

a4GlobalSpacetimePaymentReusesSelectedOrderedBudget : Bool
a4GlobalSpacetimePaymentReusesSelectedOrderedBudget = true

a5GlobalPaymentToR503CompilerClosed : Bool
a5GlobalPaymentToR503CompilerClosed = true

a3ExactSignedRateVectorPaymentTypeConstructedIsTrue :
  a3ExactSignedRateVectorPaymentTypeConstructed ≡ true
a3ExactSignedRateVectorPaymentTypeConstructedIsTrue = refl

a3QuantitativePhysicalPaymentClosedIsFalse :
  a3QuantitativePhysicalPaymentClosed ≡ false
a3QuantitativePhysicalPaymentClosedIsFalse = refl

a4GlobalSpacetimePaymentReusesSelectedOrderedBudgetIsTrue :
  a4GlobalSpacetimePaymentReusesSelectedOrderedBudget ≡ true
a4GlobalSpacetimePaymentReusesSelectedOrderedBudgetIsTrue = refl

a5GlobalPaymentToR503CompilerClosedIsTrue :
  a5GlobalPaymentToR503CompilerClosed ≡ true
a5GlobalPaymentToR503CompilerClosedIsTrue = refl
