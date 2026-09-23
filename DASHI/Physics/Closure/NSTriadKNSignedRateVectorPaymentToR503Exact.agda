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
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as PhysicalField
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentWorkDifferenceVectorBridgeExact as Vector
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalRateDifferenceExact as Rate
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299
import DASHI.Physics.Closure.NSTriadKNSignedHeatCrossToR410Round415Exact as R415
import DASHI.Physics.Closure.NSTriadKNFixedOutputSignedCrossAggregationRound432Exact as R432
import DASHI.Physics.Closure.NSTriadKNDirectResolventTrajectoryCompanionRound499Exact as R499
import DASHI.Physics.Closure.NSTriadKNDirectResolventIntegratedCompanionRound500Exact as R500
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNPhysicalTrajectoryRetainedGlobalFluxRound403Exact as R403
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

physicalFixedOutputSignedVectorRateToSeparationGeometry :
  (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F) →
  (S : Helical.HelicalModeScalars F) →
  (output : Z3.FourierMode) →
  let
    value = physicalMixedValue system S
    items = physicalOutputItems system output
    mixed = physicalMixedFold system S output
  in
  Rate.two *
    Vector.pairDifferenceVectorWorkSum
      (Rate.physicalCellRate system) mixed value items
  ≡ PhysicalField.viscosity system *
    Vector.pairDifferenceVectorWorkSum
      (Rate.separationNormSquared system) mixed value items
physicalFixedOutputSignedVectorRateToSeparationGeometry system S output =
  let
    value = physicalMixedValue system S
    items = physicalOutputItems system output
    mixed = physicalMixedFold system S output
    work = Pair.cellWork mixed value
    nu = PhysicalField.viscosity system

    physicalBridge :
      Pair.pairDifferenceWorkSum
        (Rate.physicalCellRate system) work items
      ≡ Vector.pairDifferenceVectorWorkSum
          (Rate.physicalCellRate system) mixed value items
    physicalBridge =
      Vector.pairDifferenceWorkSumIsVectorDifferenceWorkSum
        (Rate.physicalCellRate system) mixed value items

    geometricRate :
      Rate.two *
        Pair.pairDifferenceWorkSum
          (Rate.physicalCellRate system) work items
      ≡ nu * Rate.pairDifferenceGeometric system work items
    geometricRate =
      Rate.physicalOutputFiberPairDifferenceRateToGeometry
        system output work

    geometricStandard :
      Rate.pairDifferenceGeometric system work items
      ≡ Pair.pairDifferenceWorkSum
          (Rate.separationNormSquared system) work items
    geometricStandard =
      Rate.pairDifferenceGeometricIsStandardPairDifference
        system work items

    separationBridge :
      Pair.pairDifferenceWorkSum
        (Rate.separationNormSquared system) work items
      ≡ Vector.pairDifferenceVectorWorkSum
          (Rate.separationNormSquared system) mixed value items
    separationBridge =
      Vector.pairDifferenceWorkSumIsVectorDifferenceWorkSum
        (Rate.separationNormSquared system) mixed value items
  in
  trans
    (cong (Rate.two *_) (sym physicalBridge))
    (trans
      geometricRate
      (trans
        (cong (nu *_) geometricStandard)
        (cong (nu *_) separationBridge)))

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

record FixedOutputSeparationGeometryPayment
    (system : PhysicalField.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) : Set where
  field
    residualBudget : ℚ
    signedSeparationGeometryPayment :
      0ℚ -
        ( PhysicalField.viscosity system
        * Vector.pairDifferenceVectorWorkSum
            (Rate.separationNormSquared system)
            (physicalMixedFold system S output)
            (physicalMixedValue system S)
            (physicalOutputItems system output) )
      ≤ Rate.two * residualBudget

open FixedOutputSeparationGeometryPayment public

separationGeometryPaymentBuildsPhysicalRatePayment :
  ∀ {system S output} →
  FixedOutputSeparationGeometryPayment system S output →
  FixedOutputSignedRateVectorPayment system S output
separationGeometryPaymentBuildsPhysicalRatePayment
    {system} {S} {output} P = record
  { FixedOutputSignedRateVectorPayment.residualBudget =
      FixedOutputSeparationGeometryPayment.residualBudget P
  ; FixedOutputSignedRateVectorPayment.signedRateVectorPayment =
      let
        rateSum =
          Vector.pairDifferenceVectorWorkSum
            (Rate.physicalCellRate system)
            (physicalMixedFold system S output)
            (physicalMixedValue system S)
            (physicalOutputItems system output)
        geomSum =
          Vector.pairDifferenceVectorWorkSum
            (Rate.separationNormSquared system)
            (physicalMixedFold system S output)
            (physicalMixedValue system S)
            (physicalOutputItems system output)
        nu = PhysicalField.viscosity system
        budget = FixedOutputSeparationGeometryPayment.residualBudget P

        geometry :
          Rate.two * rateSum ≡ nu * geomSum
        geometry =
          physicalFixedOutputSignedVectorRateToSeparationGeometry
            system S output

        doubledPhysical :
          Rate.two * (0ℚ - rateSum)
          ≤ Rate.two * budget
        doubledPhysical =
          subst
            (λ left → left ≤ Rate.two * budget)
            (solve (rateSum ∷ nu ∷ geomSum ∷ []))
            (subst
              (λ geometric →
                0ℚ - geometric ≤ Rate.two * budget)
              (sym geometry)
              (signedSeparationGeometryPayment P))

        twoPositive : 0ℚ < Rate.two
        twoPositive =
          ℚP.+-mono-<-<
            (ℚP.positive⁻¹ 1ℚ)
            (ℚP.positive⁻¹ 1ℚ)
      in
      ℚP.*-cancelˡ-≤-pos Rate.two doubledPhysical
  }


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
-- Live A3 specialization: no caller-selected snapshot.
------------------------------------------------------------------------

module LiveA3
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Live = R403.LiveTrajectoryFlux
    Time initialTime integrateTo DerivativeOf
  module Direct499 = R499.DirectTrajectory
    Time initialTime integrateTo DerivativeOf

  physicalSystemAt :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → PhysicalField.PhysicalFiniteComplex3GalerkinSystem F
  physicalSystemAt T R cutoff time =
    Live.physicalSystemAt T
      (Support.toRetainedSupportRealization T R)
      cutoff time

  helicalScalars :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    Helical.HelicalModeScalars F
  helicalScalars T = Dyn.Base.S (Dyn.forgetDynamics T)

  ----------------------------------------------------------------------
  -- Exact aggregate bridge to the normalized quadratic slot kernel.
  --
  -- Important: this is the strongest same-object bridge actually supplied by
  -- the existing R223/R225 machinery.  It holds after summing the COMPLETE
  -- fixed-output fibre.  It does not identify one mixed (+,-) incidence with
  -- one R205 raw-curl partner cell.
  ----------------------------------------------------------------------

  liveFixedOutputQuadraticKernelIsFourMixed :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) (output : Z3.FourierMode) →
    let
      system = physicalSystemAt T R cutoff time
      S = helicalScalars T
      velocity = Audit.velocity (PhysicalField.finiteSystem system)
    in
    R224.foldVector (R225.iQuadraticKernelCell S velocity)
      (physicalOutputItems system output)
    ≡ R225.fourCopies (physicalMixedFold system S output)
  liveFixedOutputQuadraticKernelIsFourMixed
      T R cutoff time output =
    let
      module At = Direct499.Flux.At T R cutoff time
    in
    R225.fixedOutputQuadraticKernelIsFourMixedHelicityConvolution
      At.P cutoff output

  LiveFixedOutputSignedRateVectorPayment :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → Z3.FourierMode → Set
  LiveFixedOutputSignedRateVectorPayment T R cutoff time output =
    FixedOutputSignedRateVectorPayment
      (physicalSystemAt T R cutoff time)
      (helicalScalars T)
      output


  LiveFixedOutputSeparationGeometryPayment :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → Z3.FourierMode → Set
  LiveFixedOutputSeparationGeometryPayment T R cutoff time output =
    FixedOutputSeparationGeometryPayment
      (physicalSystemAt T R cutoff time)
      (helicalScalars T)
      output

  liveSeparationPaymentBuildsPhysicalRatePayment :
    ∀ {T R cutoff time output} →
    LiveFixedOutputSeparationGeometryPayment T R cutoff time output →
    LiveFixedOutputSignedRateVectorPayment T R cutoff time output
  liveSeparationPaymentBuildsPhysicalRatePayment =
    separationGeometryPaymentBuildsPhysicalRatePayment

  livePaymentToR432Datatype :
    ∀ {T R cutoff time output} →
    LiveFixedOutputSignedRateVectorPayment T R cutoff time output →
    R432.FixedOutputSignedCrossPayment
  livePaymentToR432Datatype = a3PaymentToR432

  ----------------------------------------------------------------------
  -- Selected-output A3 family and cardinality-free instantaneous sum.
  ----------------------------------------------------------------------

  data LivePaymentFamilyOn
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (cutoff : Nat) (time : Time) :
      List Z3.FourierMode → Set where
    paymentNil : LivePaymentFamilyOn T R cutoff time []
    paymentCons :
      ∀ {output outputs} →
      LiveFixedOutputSignedRateVectorPayment T R cutoff time output →
      LivePaymentFamilyOn T R cutoff time outputs →
      LivePaymentFamilyOn T R cutoff time (output ∷ outputs)

  paymentList :
    ∀ {T R cutoff time outputs} →
    LivePaymentFamilyOn T R cutoff time outputs →
    List R432.FixedOutputSignedCrossPayment
  paymentList paymentNil = []
  paymentList (paymentCons head tail) =
    livePaymentToR432Datatype head ∷ paymentList tail


  data LiveSeparationPaymentFamilyOn
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (cutoff : Nat) (time : Time) :
      List Z3.FourierMode → Set where
    separationPaymentNil :
      LiveSeparationPaymentFamilyOn T R cutoff time []
    separationPaymentCons :
      ∀ {output outputs} →
      LiveFixedOutputSeparationGeometryPayment T R cutoff time output →
      LiveSeparationPaymentFamilyOn T R cutoff time outputs →
      LiveSeparationPaymentFamilyOn T R cutoff time (output ∷ outputs)

  separationFamilyToPhysical :
    ∀ {T R cutoff time outputs} →
    LiveSeparationPaymentFamilyOn T R cutoff time outputs →
    LivePaymentFamilyOn T R cutoff time outputs
  separationFamilyToPhysical separationPaymentNil = paymentNil
  separationFamilyToPhysical (separationPaymentCons head tail) =
    paymentCons
      (liveSeparationPaymentBuildsPhysicalRatePayment head)
      (separationFamilyToPhysical tail)

  separationPaymentList :
    ∀ {T R cutoff time outputs} →
    LiveSeparationPaymentFamilyOn T R cutoff time outputs →
    List R432.FixedOutputSignedCrossPayment
  separationPaymentList family =
    paymentList (separationFamilyToPhysical family)


  sumSignedRateVectorPayment :
    ∀ {T R cutoff time outputs} →
    LivePaymentFamilyOn T R cutoff time outputs → ℚ
  sumSignedRateVectorPayment family =
    R432.sumSignedCross (paymentList family)

  sumResidualBudgets :
    ∀ {T R cutoff time outputs} →
    LivePaymentFamilyOn T R cutoff time outputs → ℚ
  sumResidualBudgets family =
    R432.sumFibreBudget (paymentList family)

  liveA3FamilySumWithoutOutputCardinalityFactor :
    ∀ {T R cutoff time outputs} →
    (family : LivePaymentFamilyOn T R cutoff time outputs) →
    sumSignedRateVectorPayment family ≤ sumResidualBudgets family
  liveA3FamilySumWithoutOutputCardinalityFactor family =
    R432.fixedOutputBudgetsSumWithoutCardinalityFactor
      (paymentList family)

  ----------------------------------------------------------------------
  -- Consumer attachment boundary.
  --
  -- IMPORTANT CORRECTION:
  -- the signed rate/vector pair sum is the coherent VISCOUS-COVARIANCE
  -- residual.  R406.weightedRemainder is the resolvent-weighted NONLINEAR
  -- Gram remainder.  They are connected through the already-proved damped
  -- tangent / endpoint decomposition; they are not the same scalar by
  -- definition.  Therefore the old direct-equality receipt below is retained
  -- only as a legacy over-strong interface and is explicitly non-mandatory.
  --
  -- The admissible interface is theorem-bearing: a local A3 payment must be
  -- transported through the coherent decomposition (including its endpoint
  -- term) to the actual fixed-output signed-cross consumer.
  ----------------------------------------------------------------------

  liveR406Outputs :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → List Z3.FourierMode
  liveR406Outputs T R cutoff time =
    Direct499.Flux.At.outputs T R cutoff time

  CanonicalLivePaymentFamily :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → Set
  CanonicalLivePaymentFamily T R cutoff time =
    LivePaymentFamilyOn T R cutoff time
      (liveR406Outputs T R cutoff time)


  CanonicalLiveSeparationPaymentFamily :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → Set
  CanonicalLiveSeparationPaymentFamily T R cutoff time =
    LiveSeparationPaymentFamilyOn T R cutoff time
      (liveR406Outputs T R cutoff time)

  canonicalSeparationFamilyToPhysical :
    ∀ {T R cutoff time} →
    CanonicalLiveSeparationPaymentFamily T R cutoff time →
    CanonicalLivePaymentFamily T R cutoff time
  canonicalSeparationFamilyToPhysical = separationFamilyToPhysical

  record LiveA3ToR406Attachment
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (cutoff : Nat) (time : Time)
      (family : CanonicalLivePaymentFamily T R cutoff time) : Set where
    field
      literalR406IsFourSignedRateVectorSum :
        Direct499.Flux.At.weightedRemainder T R cutoff time
        ≡ R299.four * sumSignedRateVectorPayment family

  open LiveA3ToR406Attachment public

  -- Correct consumer-facing receipt.  This does NOT assert equality between
  -- covariance and R406.  It records the exact signed cross seen by the
  -- downstream R432 compiler after the endpoint/covariance decomposition has
  -- been performed on this same live slice.
  record LiveA3ConsumerAttachment
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (cutoff : Nat) (time : Time)
      (output : Z3.FourierMode)
      (payment : LiveFixedOutputSignedRateVectorPayment
        T R cutoff time output) : Set where
    field
      literalFixedOutputSignedCross : ℚ

      a3PaymentIsConsumerSignedCross :
        literalFixedOutputSignedCross
        ≡ 0ℚ - Vector.pairDifferenceVectorWorkSum
            (Rate.physicalCellRate (physicalSystemAt T R cutoff time))
            (physicalMixedFold
              (physicalSystemAt T R cutoff time)
              (helicalScalars T) output)
            (physicalMixedValue
              (physicalSystemAt T R cutoff time)
              (helicalScalars T))
            (physicalOutputItems
              (physicalSystemAt T R cutoff time) output)

      consumerSignedCrossBound :
        literalFixedOutputSignedCross ≤
        FixedOutputSignedRateVectorPayment.residualBudget payment

  open LiveA3ConsumerAttachment public

  liveA3ConsumerAttachmentBuildsR432Payment :
    ∀ {T R cutoff time output payment} →
    LiveA3ConsumerAttachment T R cutoff time output payment →
    R432.FixedOutputSignedCrossPayment
  liveA3ConsumerAttachmentBuildsR432Payment {payment = payment} A =
    R432.fixed-output-signed-cross-payment
      (literalFixedOutputSignedCross A)
      (FixedOutputSignedRateVectorPayment.residualBudget payment)
      (consumerSignedCrossBound A)


  LiveSeparationA3ToR406Attachment :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    CanonicalLiveSeparationPaymentFamily T R cutoff time → Set
  LiveSeparationA3ToR406Attachment T R cutoff time family =
    LiveA3ToR406Attachment
      T R cutoff time
      (canonicalSeparationFamilyToPhysical family)


  -- Preferred consumer transport: A4 requires only this inequality.  A proof
  -- may obtain it from d1b0+d1b1 (endpoint/tangent) plus the A3 covariance
  -- payment; no direct covariance=R406 identity is requested.
  record LiveA3R406BudgetAttachment
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (cutoff : Nat) (time : Time)
      (family : CanonicalLivePaymentFamily T R cutoff time) : Set where
    field
      literalR406PaidByA3Budgets :
        Direct499.Flux.At.weightedRemainder T R cutoff time
        ≤ R299.four * sumResidualBudgets family

  open LiveA3R406BudgetAttachment public

  LiveSeparationA3R406BudgetAttachment :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    CanonicalLiveSeparationPaymentFamily T R cutoff time → Set
  LiveSeparationA3R406BudgetAttachment T R cutoff time family =
    LiveA3R406BudgetAttachment
      T R cutoff time
      (canonicalSeparationFamilyToPhysical family)

------------------------------------------------------------------------
-- Standard ordered-integration authority.
--
-- R495 intentionally records only equality/additivity transport.  A4 needs
-- the ordinary monotonicity theorem for the concrete temporal integral.
-- Keeping it separate prevents an abstract integrateTo function from gaining
-- an order theorem by fiat.
------------------------------------------------------------------------

record IntegrationOrderAuthority
    (Time : Set)
    (integrateTo : (Time → ℚ) → Time → ℚ) : Set₁ where
  field
    integrateMonotone :
      (f g : Time → ℚ) →
      ((time : Time) → f time ≤ g time) →
      (terminal : Time) →
      integrateTo f terminal ≤ integrateTo g terminal

open IntegrationOrderAuthority public

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
  -- Live A3 -> A4 compiler using only ordinary integration monotonicity.
  ----------------------------------------------------------------------

  module Local = LiveA3 Time initialTime integrateTo DerivativeOf

  fourNonnegative : 0ℚ ≤ R299.four
  fourNonnegative =
    Rational.addNonnegative
      (Rational.addNonnegative
        Rational.oneNonnegative Rational.oneNonnegative)
      (Rational.addNonnegative
        Rational.oneNonnegative Rational.oneNonnegative)

  fourTimesMonotone :
    ∀ {left right : ℚ} → left ≤ right →
    R299.four * left ≤ R299.four * right
  fourTimesMonotone lower =
    let instance fourNN = nonNegative fourNonnegative
    in ℚP.*-monoˡ-≤-nonNeg R299.four lower

  record LiveA3SpacetimeProducer
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      familyAt :
        (cutoff : Nat) (time : Time) →
        Local.CanonicalLivePaymentFamily T R cutoff time

      attachmentAt :
        (cutoff : Nat) (time : Time) →
        Local.LiveA3R406BudgetAttachment
          T R cutoff time (familyAt cutoff time)

      cutoffIndependentBound : Time → ℚ

      integratedResidualBudgetsPaid :
        (cutoff : Nat) (terminal : Time) →
        integrateTo
          (λ time →
            R299.four
              * Local.sumResidualBudgets (familyAt cutoff time))
          terminal
        ≤ cutoffIndependentBound terminal

  open LiveA3SpacetimeProducer public

  liveR406PointwiseUpper :
    ∀ {T R} →
    (P : LiveA3SpacetimeProducer T R) →
    (cutoff : Nat) (time : Time) →
    Local.Direct499.Flux.At.weightedRemainder T R cutoff time
    ≤ R299.four * Local.sumResidualBudgets (familyAt P cutoff time)
  liveR406PointwiseUpper P cutoff time =
    Local.literalR406PaidByA3Budgets (attachmentAt P cutoff time)

  liveA3IntegratedRemainderUpper :
    (orderIntegration : IntegrationOrderAuthority Time integrateTo) →
    ∀ {T R} →
    (P : LiveA3SpacetimeProducer T R) →
    (cutoff : Nat) (terminal : Time) →
    Heat.literalRemainderIntegral T R cutoff terminal
    ≤ cutoffIndependentBound P terminal
  liveA3IntegratedRemainderUpper orderIntegration {T} {R} P cutoff terminal =
    ℚP.≤-trans
      (integrateMonotone orderIntegration
        (λ time → Local.Direct499.Flux.At.weightedRemainder T R cutoff time)
        (λ time →
          R299.four
            * Local.sumResidualBudgets (familyAt P cutoff time))
        (liveR406PointwiseUpper P cutoff)
        terminal)
      (integratedResidualBudgetsPaid P cutoff terminal)

  liveA3SpacetimeBuildsDirectOffDiagonalBudget :
    (orderIntegration : IntegrationOrderAuthority Time integrateTo) →
    ∀ {T R} →
    LiveA3SpacetimeProducer T R →
    DirectBudget.DirectOffDiagonalBudget T R
  liveA3SpacetimeBuildsDirectOffDiagonalBudget orderIntegration {T} {R} P = record
    { DirectBudget.cutoffIndependentBound = cutoffIndependentBound P
    ; DirectBudget.directOffDiagonalBudget = λ cutoff terminal →
        subst
          (λ lhs → lhs ≤ cutoffIndependentBound P terminal)
          (Direct.literalR406IntegralIsFourIntegratedDirectCompanion
            T R cutoff terminal)
          (liveA3IntegratedRemainderUpper
            orderIntegration P cutoff terminal)
    }

  ----------------------------------------------------------------------
  -- Preferred geometric A3 producer.  This is the same live compiler, but
  -- theorem search is stated directly on the squared separation geometry.
  ----------------------------------------------------------------------

  record LiveSeparationA3SpacetimeProducer
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      separationFamilyAt :
        (cutoff : Nat) (time : Time) →
        Local.CanonicalLiveSeparationPaymentFamily T R cutoff time

      separationAttachmentAt :
        (cutoff : Nat) (time : Time) →
        Local.LiveSeparationA3R406BudgetAttachment
          T R cutoff time (separationFamilyAt cutoff time)

      cutoffIndependentBound : Time → ℚ

      integratedResidualBudgetsPaid :
        (cutoff : Nat) (terminal : Time) →
        integrateTo
          (λ time →
            R299.four
              * Local.sumResidualBudgets
                  (Local.canonicalSeparationFamilyToPhysical
                    (separationFamilyAt cutoff time)))
          terminal
        ≤ cutoffIndependentBound terminal

  open LiveSeparationA3SpacetimeProducer public

  separationProducerToPhysical :
    ∀ {T R} →
    LiveSeparationA3SpacetimeProducer T R →
    LiveA3SpacetimeProducer T R
  separationProducerToPhysical P = record
    { familyAt = λ cutoff time →
        Local.canonicalSeparationFamilyToPhysical
          (separationFamilyAt P cutoff time)
    ; attachmentAt = λ cutoff time →
        separationAttachmentAt P cutoff time
    ; cutoffIndependentBound =
        LiveSeparationA3SpacetimeProducer.cutoffIndependentBound P
    ; integratedResidualBudgetsPaid =
        LiveSeparationA3SpacetimeProducer.integratedResidualBudgetsPaid P
    }

  liveSeparationA3SpacetimeBuildsDirectOffDiagonalBudget :
    (orderIntegration : IntegrationOrderAuthority Time integrateTo) →
    ∀ {T R} →
    LiveSeparationA3SpacetimeProducer T R →
    DirectBudget.DirectOffDiagonalBudget T R
  liveSeparationA3SpacetimeBuildsDirectOffDiagonalBudget
      orderIntegration P =
    liveA3SpacetimeBuildsDirectOffDiagonalBudget
      orderIntegration (separationProducerToPhysical P)

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

a3RateWorkCorrelationReducedToSeparationGeometry : Bool
a3RateWorkCorrelationReducedToSeparationGeometry = true

a3SeparationGeometryPaymentCompilerClosed : Bool
a3SeparationGeometryPaymentCompilerClosed = true

a3PreferredLiveSeparationGeometryCompilerClosed : Bool
a3PreferredLiveSeparationGeometryCompilerClosed = true

a3RecordIsLiteralPhysicalFixedOutputFamily : Bool
a3RecordIsLiteralPhysicalFixedOutputFamily = true

a3QuantitativePhysicalPaymentClosed : Bool
a3QuantitativePhysicalPaymentClosed = false

a3PaymentPackagesInR432FixedOutputPaymentDatatype : Bool
a3PaymentPackagesInR432FixedOutputPaymentDatatype = true

a3DirectCovarianceEqualsR406RemainderAdmissible : Bool
a3DirectCovarianceEqualsR406RemainderAdmissible = false

-- Legacy direct-equality interface remains uninhabited and is no longer a
-- mandatory seam.
a3ToR432LiteralR406SameObjectAttachmentClosed : Bool
a3ToR432LiteralR406SameObjectAttachmentClosed = false

a3ConsumerAttachmentTypeConstructed : Bool
a3ConsumerAttachmentTypeConstructed = true

a3PreferredR406BudgetAttachmentTypeConstructed : Bool
a3PreferredR406BudgetAttachmentTypeConstructed = true

a3PreferredCompilerRequiresDirectCovarianceR406Equality : Bool
a3PreferredCompilerRequiresDirectCovarianceR406Equality = false

a3NormalizedQuadraticKernelAggregateBridgeClosed : Bool
a3NormalizedQuadraticKernelAggregateBridgeClosed = true

-- The stronger pointwise identification
--   mixedPlusMinus(tau) = R205 compressedPartnerVector(tau)
-- is not what R223/R225 prove.  R225 supplies only the complete-fibre
-- normalized-kernel collapse above, while R205 is an unnormalized raw-curl
-- partner carrier.  Keep this fail-closed.
a3R205RawCurlPartnerSameObjectBridgeClosed : Bool
a3R205RawCurlPartnerSameObjectBridgeClosed = false

a3R205PointwiseIdentificationAdmissible : Bool
a3R205PointwiseIdentificationAdmissible = false

liveA3SnapshotBoundToR240Trajectory : Bool
liveA3SnapshotBoundToR240Trajectory = true

liveA3SelectedOutputAggregationClosed : Bool
liveA3SelectedOutputAggregationClosed = true

liveA3ToR406AttachmentTypeConstructed : Bool
liveA3ToR406AttachmentTypeConstructed = true

a4CardinalityFreeLocalToGlobalCompilerClosed : Bool
a4CardinalityFreeLocalToGlobalCompilerClosed = true

a4OrderPreservingIntegrationCompilerClosed : Bool
a4OrderPreservingIntegrationCompilerClosed = true

a4IntegrationMonotonicityIsStandardAuthority : Bool
a4IntegrationMonotonicityIsStandardAuthority = true

a4CutoffUniformSumStillAnalyticInput : Bool
a4CutoffUniformSumStillAnalyticInput = true

a4GlobalSpacetimePaymentReusesSelectedOrderedBudget : Bool
a4GlobalSpacetimePaymentReusesSelectedOrderedBudget = true

a5GlobalPaymentToR503CompilerClosed : Bool
a5GlobalPaymentToR503CompilerClosed = true

a3ExactSignedRateVectorPaymentTypeConstructedIsTrue :
  a3ExactSignedRateVectorPaymentTypeConstructed ≡ true
a3ExactSignedRateVectorPaymentTypeConstructedIsTrue = refl

a3RateWorkCorrelationReducedToSeparationGeometryIsTrue :
  a3RateWorkCorrelationReducedToSeparationGeometry ≡ true
a3RateWorkCorrelationReducedToSeparationGeometryIsTrue = refl

a3SeparationGeometryPaymentCompilerClosedIsTrue :
  a3SeparationGeometryPaymentCompilerClosed ≡ true
a3SeparationGeometryPaymentCompilerClosedIsTrue = refl

a3PreferredLiveSeparationGeometryCompilerClosedIsTrue :
  a3PreferredLiveSeparationGeometryCompilerClosed ≡ true
a3PreferredLiveSeparationGeometryCompilerClosedIsTrue = refl

a3RecordIsLiteralPhysicalFixedOutputFamilyIsTrue :
  a3RecordIsLiteralPhysicalFixedOutputFamily ≡ true
a3RecordIsLiteralPhysicalFixedOutputFamilyIsTrue = refl

a3QuantitativePhysicalPaymentClosedIsFalse :
  a3QuantitativePhysicalPaymentClosed ≡ false
a3QuantitativePhysicalPaymentClosedIsFalse = refl

a3PaymentPackagesInR432FixedOutputPaymentDatatypeIsTrue :
  a3PaymentPackagesInR432FixedOutputPaymentDatatype ≡ true
a3PaymentPackagesInR432FixedOutputPaymentDatatypeIsTrue = refl

a3DirectCovarianceEqualsR406RemainderAdmissibleIsFalse :
  a3DirectCovarianceEqualsR406RemainderAdmissible ≡ false
a3DirectCovarianceEqualsR406RemainderAdmissibleIsFalse = refl

a3ToR432LiteralR406SameObjectAttachmentClosedIsFalse :
  a3ToR432LiteralR406SameObjectAttachmentClosed ≡ false
a3ToR432LiteralR406SameObjectAttachmentClosedIsFalse = refl

a3ConsumerAttachmentTypeConstructedIsTrue :
  a3ConsumerAttachmentTypeConstructed ≡ true
a3ConsumerAttachmentTypeConstructedIsTrue = refl

a3PreferredR406BudgetAttachmentTypeConstructedIsTrue :
  a3PreferredR406BudgetAttachmentTypeConstructed ≡ true
a3PreferredR406BudgetAttachmentTypeConstructedIsTrue = refl

a3PreferredCompilerRequiresDirectCovarianceR406EqualityIsFalse :
  a3PreferredCompilerRequiresDirectCovarianceR406Equality ≡ false
a3PreferredCompilerRequiresDirectCovarianceR406EqualityIsFalse = refl

a3NormalizedQuadraticKernelAggregateBridgeClosedIsTrue :
  a3NormalizedQuadraticKernelAggregateBridgeClosed ≡ true
a3NormalizedQuadraticKernelAggregateBridgeClosedIsTrue = refl

a3R205RawCurlPartnerSameObjectBridgeClosedIsFalse :
  a3R205RawCurlPartnerSameObjectBridgeClosed ≡ false
a3R205RawCurlPartnerSameObjectBridgeClosedIsFalse = refl

a3R205PointwiseIdentificationAdmissibleIsFalse :
  a3R205PointwiseIdentificationAdmissible ≡ false
a3R205PointwiseIdentificationAdmissibleIsFalse = refl

liveA3SelectedOutputAggregationClosedIsTrue :
  liveA3SelectedOutputAggregationClosed ≡ true
liveA3SelectedOutputAggregationClosedIsTrue = refl

liveA3ToR406AttachmentTypeConstructedIsTrue :
  liveA3ToR406AttachmentTypeConstructed ≡ true
liveA3ToR406AttachmentTypeConstructedIsTrue = refl

liveA3SnapshotBoundToR240TrajectoryIsTrue :
  liveA3SnapshotBoundToR240Trajectory ≡ true
liveA3SnapshotBoundToR240TrajectoryIsTrue = refl

a4CardinalityFreeLocalToGlobalCompilerClosedIsTrue :
  a4CardinalityFreeLocalToGlobalCompilerClosed ≡ true
a4CardinalityFreeLocalToGlobalCompilerClosedIsTrue = refl

a4OrderPreservingIntegrationCompilerClosedIsTrue :
  a4OrderPreservingIntegrationCompilerClosed ≡ true
a4OrderPreservingIntegrationCompilerClosedIsTrue = refl

a4IntegrationMonotonicityIsStandardAuthorityIsTrue :
  a4IntegrationMonotonicityIsStandardAuthority ≡ true
a4IntegrationMonotonicityIsStandardAuthorityIsTrue = refl

a4CutoffUniformSumStillAnalyticInputIsTrue :
  a4CutoffUniformSumStillAnalyticInput ≡ true
a4CutoffUniformSumStillAnalyticInputIsTrue = refl

a4GlobalSpacetimePaymentReusesSelectedOrderedBudgetIsTrue :
  a4GlobalSpacetimePaymentReusesSelectedOrderedBudget ≡ true
a4GlobalSpacetimePaymentReusesSelectedOrderedBudgetIsTrue = refl

a5GlobalPaymentToR503CompilerClosedIsTrue :
  a5GlobalPaymentToR503CompilerClosed ≡ true
a5GlobalPaymentToR503CompilerClosedIsTrue = refl
