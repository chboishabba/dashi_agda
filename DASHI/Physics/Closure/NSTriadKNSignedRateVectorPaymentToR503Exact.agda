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
open import Data.Rational.Base using (ℚ; 0ℚ; _-_; _≤_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as PhysicalField
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentWorkDifferenceVectorBridgeExact as Vector
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateDifferenceExact as Rate
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNSignedHeatCrossToR410Round415Exact as R415
import DASHI.Physics.Closure.NSTriadKNFixedOutputSignedCrossAggregationRound432Exact as R432
import DASHI.Physics.Closure.NSTriadKNDirectResolventIntegratedCompanionRound500Exact as R500
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

physicalMixedValue :
  (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F) →
  Helical.HelicalModeScalars F →
  Physical.PhysicalTriadIncidence → C3.Complex3 F
physicalMixedValue system S =
  D1a.mixedProductCell S
    (Audit.velocity (PhysicalField.finiteSystem system))

physicalOutputItems :
  PhysicalField.PhysicalFiniteComplex3GalerkinSystem F →
  Z3.FourierMode → List Physical.PhysicalTriadIncidence
physicalOutputItems system output =
  Output.physicalOutputFiber
    (Audit.cutoff (PhysicalField.finiteSystem system)) output

physicalMixedFold :
  (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F) →
  (S : Helical.HelicalModeScalars F) →
  Z3.FourierMode → C3.Complex3 F
physicalMixedFold system S output =
  R224.foldVector
    (physicalMixedValue system S)
    (physicalOutputItems system output)

record FixedOutputSignedRateVectorPayment
    (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) : Set where
  field
    residualBudget : ℚ
    signedRateVectorPayment :
      0ℚ - Vector.pairDifferenceVectorWorkSum
          (Rate.physicalCellRate system)
          (physicalMixedFold system S output)
          (physicalMixedValue system S)
          (physicalOutputItems system output)
      ≤ residualBudget

open FixedOutputSignedRateVectorPayment public

a3PaymentToR432 :
  ∀ {system S output} →
  FixedOutputSignedRateVectorPayment system S output →
  R432.FixedOutputSignedCrossPayment
a3PaymentToR432 {system} {S} {output} P =
  R432.fixed-output-signed-cross-payment
    (0ℚ - Vector.pairDifferenceVectorWorkSum
      (Rate.physicalCellRate system)
      (physicalMixedFold system S output)
      (physicalMixedValue system S)
      (physicalOutputItems system output))
    (residualBudget P)
    (signedRateVectorPayment P)

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

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Heat = R415.SignedHeatCross
    Time initialTime integrateTo DerivativeOf
  module Direct = R500.IntegratedDirect
    Time initialTime integrateTo DerivativeOf integration
  module DirectBudget = R503.DirectSignedCross
    Time initialTime integrateTo DerivativeOf integration
  module Ordered = OrderedToR503.OrderedToR503
    Time initialTime integrateTo DerivativeOf integration

  ----------------------------------------------------------------------
  -- A4, direct fixed-output formulation.
  --
  -- decomposition is the theorem-bearing list of local A3 payments after
  -- conversion to R432. R432 supplies the cardinality-free finite summation.
  -- The only global analytic field is summedFibreBudgetsPaid.
  ----------------------------------------------------------------------

  record S2b2LocalToGlobalProducer
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      decomposition :
        Nat → Time → R432.FixedOutputRemainderDecomposition

      literalRemainderIsDecomposition :
        (cutoff : Nat) (terminal : Time) →
        Heat.literalRemainderIntegral T R cutoff terminal
        ≡ R432.globalWeightedRemainder (decomposition cutoff terminal)

      cutoffIndependentBound : Time → ℚ

      summedFibreBudgetsPaid :
        (cutoff : Nat) (terminal : Time) →
        R299.four
          * R432.sumFibreBudget
              (R432.payments (decomposition cutoff terminal))
        ≤ cutoffIndependentBound terminal

  open S2b2LocalToGlobalProducer public

  literalRemainderUpper :
    ∀ {T R} →
    (P : S2b2LocalToGlobalProducer T R) →
    (cutoff : Nat) (terminal : Time) →
    Heat.literalRemainderIntegral T R cutoff terminal
    ≤ cutoffIndependentBound P terminal
  literalRemainderUpper {T} {R} P cutoff terminal =
    let
      D = decomposition P cutoff terminal

      localSum :
        R432.globalWeightedRemainder D
        ≤ R299.four * R432.sumFibreBudget (R432.payments D)
      localSum = R432.fixedOutputPaymentsBoundGlobalRemainder D

      physicalSum :
        Heat.literalRemainderIntegral T R cutoff terminal
        ≤ R299.four * R432.sumFibreBudget (R432.payments D)
      physicalSum =
        subst
          (λ lower →
            lower ≤ R299.four * R432.sumFibreBudget (R432.payments D))
          (sym (literalRemainderIsDecomposition P cutoff terminal))
          localSum
    in
    ℚP.≤-trans physicalSum (summedFibreBudgetsPaid P cutoff terminal)

  ----------------------------------------------------------------------
  -- A5: direct compiler to the canonical R503 consumer.
  ----------------------------------------------------------------------

  s2b2LocalPaymentsBuildDirectOffDiagonalBudget :
    ∀ {T R} →
    S2b2LocalToGlobalProducer T R →
    DirectBudget.DirectOffDiagonalBudget T R
  s2b2LocalPaymentsBuildDirectOffDiagonalBudget {T} {R} P = record
    { DirectBudget.cutoffIndependentBound = cutoffIndependentBound P
    ; DirectBudget.directOffDiagonalBudget = λ cutoff terminal →
        subst
          (λ lhs → lhs ≤ cutoffIndependentBound P terminal)
          (Direct.literalR406IntegralIsFourIntegratedDirectCompanion
            T R cutoff terminal)
          (literalRemainderUpper P cutoff terminal)
    }

  ----------------------------------------------------------------------
  -- Existing ordered-kernel formulation remains a downstream producer
  -- interface when a proof is stated there directly.
  ----------------------------------------------------------------------

  S2b2GlobalSpacetimePayment :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    Support.LiteralNonzeroCutoffTrajectory T → Set₁
  S2b2GlobalSpacetimePayment = Ordered.OrderedOrientedSpacetimeBudget

  s2b2OrderedPaymentBuildsDirectOffDiagonalBudget :
    ∀ {T R} →
    S2b2GlobalSpacetimePayment T R →
    DirectBudget.DirectOffDiagonalBudget T R
  s2b2OrderedPaymentBuildsDirectOffDiagonalBudget =
    Ordered.orderedBudgetBuildsR503
------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

a3ExactSignedRateVectorPaymentTypeConstructed : Bool
a3ExactSignedRateVectorPaymentTypeConstructed = true

a3RecordIsLiteralPhysicalFixedOutputFamily : Bool
a3RecordIsLiteralPhysicalFixedOutputFamily = true

a3QuantitativePhysicalPaymentClosed : Bool
a3QuantitativePhysicalPaymentClosed = false

a3PaymentConvertsToR432FixedOutputPayment : Bool
a3PaymentConvertsToR432FixedOutputPayment = true

a4CardinalityFreeLocalToGlobalCompilerClosed : Bool
a4CardinalityFreeLocalToGlobalCompilerClosed = true

a4CutoffUniformSumStillAnalyticInput : Bool
a4CutoffUniformSumStillAnalyticInput = true

a4GlobalSpacetimePaymentReusesSelectedOrderedBudget : Bool
a4GlobalSpacetimePaymentReusesSelectedOrderedBudget = true

a5GlobalPaymentToR503CompilerClosed : Bool
a5GlobalPaymentToR503CompilerClosed = true

a3ExactSignedRateVectorPaymentTypeConstructedIsTrue :
  a3ExactSignedRateVectorPaymentTypeConstructed ≡ true
a3ExactSignedRateVectorPaymentTypeConstructedIsTrue = refl

a3RecordIsLiteralPhysicalFixedOutputFamilyIsTrue :
  a3RecordIsLiteralPhysicalFixedOutputFamily ≡ true
a3RecordIsLiteralPhysicalFixedOutputFamilyIsTrue = refl

a3QuantitativePhysicalPaymentClosedIsFalse :
  a3QuantitativePhysicalPaymentClosed ≡ false
a3QuantitativePhysicalPaymentClosedIsFalse = refl

a3PaymentConvertsToR432FixedOutputPaymentIsTrue :
  a3PaymentConvertsToR432FixedOutputPayment ≡ true
a3PaymentConvertsToR432FixedOutputPaymentIsTrue = refl

a4CardinalityFreeLocalToGlobalCompilerClosedIsTrue :
  a4CardinalityFreeLocalToGlobalCompilerClosed ≡ true
a4CardinalityFreeLocalToGlobalCompilerClosedIsTrue = refl

a4CutoffUniformSumStillAnalyticInputIsTrue :
  a4CutoffUniformSumStillAnalyticInput ≡ true
a4CutoffUniformSumStillAnalyticInputIsTrue = refl

a4GlobalSpacetimePaymentReusesSelectedOrderedBudgetIsTrue :
  a4GlobalSpacetimePaymentReusesSelectedOrderedBudget ≡ true
a4GlobalSpacetimePaymentReusesSelectedOrderedBudgetIsTrue = refl

a5GlobalPaymentToR503CompilerClosedIsTrue :
  a5GlobalPaymentToR503CompilerClosed ≡ true
a5GlobalPaymentToR503CompilerClosedIsTrue = refl
