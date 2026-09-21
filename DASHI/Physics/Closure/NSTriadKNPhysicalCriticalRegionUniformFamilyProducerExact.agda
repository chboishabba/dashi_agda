module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionUniformFamilyProducerExact where

------------------------------------------------------------------------
-- S2b2d1b2 / ANALYTIC LEAVES -> NATIVE R236 UNIFORM FAMILY
--
-- This file pays the B5/B6 record-construction seam exactly.  It does not
-- assume or postulate any shell/covariance theorem: a caller supplies the
-- four theorem-bearing analytic receipts for each output.  The compiler then
-- constructs the literal PhysicalCriticalRegionPayment and the existing
-- UniformPhysicalCriticalRegionFamily with a definitionally fixed theta and
-- the literal selected-pair local ED currency.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _<_; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNPhysicalRawCurlCellEDAdapterRound219Exact as R219
import DASHI.Physics.Closure.NSTriadKNSelectedPairPhysicalTriadRoutingRound469Exact as R469
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact as Pay
import DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionUniformFamilyExact as Uniform

F : C3.RealField _
F = Rational.rationalRealField

module Producer
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (theta coefficient : ℚ)
    (select : Z3.FourierMode → Z3.FourierMode → Bool) where

  E = Field30.physicalEmbedding physicalSystem
  I = Field30.physicalInverseSquare physicalSystem
  system = Field30.finiteSystem physicalSystem
  velocity = Audit.velocity system
  cutoff = Audit.cutoff system
  nu = Field30.viscosity physicalSystem

  module U = Uniform.UniformFamily physicalSystem S theta coefficient select

  localED : Z3.FourierMode → ℚ
  localED output =
    R38.foldPower
      (R469.selectedTriadValue
        (R219.physicalModalED E I velocity) select)
      (Output.physicalOutputFiber cutoff output)

  record PerOutputAnalyticReceipts
      (output : Z3.FourierMode) : Set where
    constructor per-output-analytic-receipts
    field
      deepFarLowFarLowBudget
      deepFarLowDeepHighHighBudget
      deepHighHighHighHighBudget
      coreCompanionMass
      coreEDBudget : ℚ

      viscosityNN : 0ℚ ≤ nu
      thetaNN : 0ℚ ≤ theta
      thetaStrictlyBelowOne : theta < 1

      deepFarLowFarLowPaid :
        let module P = Pay.LiveRegionPayment physicalSystem S output
        in P.deepFarLowFarLowSigned ≤ deepFarLowFarLowBudget

      deepFarLowDeepHighHighPaid :
        let module P = Pay.LiveRegionPayment physicalSystem S output
        in P.deepFarLowDeepHighHighSigned ≤ deepFarLowDeepHighHighBudget

      deepHighHighHighHighPaid :
        let module P = Pay.LiveRegionPayment physicalSystem S output
        in P.deepHighHighHighHighSigned ≤ deepHighHighHighHighBudget

      criticalTouchingRelativeCovariance :
        let module P = Pay.LiveRegionPayment physicalSystem S output
        in
        P.criticalTouchingSigned
        ≤ theta * coreCompanionMass + coreEDBudget

  open PerOutputAnalyticReceipts public

  paymentAt :
    (output : Z3.FourierMode) →
    PerOutputAnalyticReceipts output →
    let module P = Pay.LiveRegionPayment physicalSystem S output
    in P.PhysicalCriticalRegionPayment
  paymentAt output receipts =
    let module P = Pay.LiveRegionPayment physicalSystem S output
    in record
      { P.deepFarLowFarLowBudget = deepFarLowFarLowBudget receipts
      ; P.deepFarLowDeepHighHighBudget = deepFarLowDeepHighHighBudget receipts
      ; P.deepHighHighHighHighBudget = deepHighHighHighHighBudget receipts
      ; P.coreCompanionMass = coreCompanionMass receipts
      ; P.coreEDBudget = coreEDBudget receipts
      ; P.theta = theta
      ; P.viscosityNN = viscosityNN receipts
      ; P.thetaNN = thetaNN receipts
      ; P.thetaStrictlyBelowOne = thetaStrictlyBelowOne receipts
      ; P.deepFarLowFarLowPaid = deepFarLowFarLowPaid receipts
      ; P.deepFarLowDeepHighHighPaid = deepFarLowDeepHighHighPaid receipts
      ; P.deepHighHighHighHighPaid = deepHighHighHighHighPaid receipts
      ; P.criticalTouchingRelativeCovariance =
          criticalTouchingRelativeCovariance receipts
      }

  record UniformAnalyticReceipts : Set₁ where
    constructor uniform-analytic-receipts
    field
      receiptsAt :
        (output : Z3.FourierMode) → PerOutputAnalyticReceipts output

      coefficientNN : 0ℚ ≤ coefficient
      viscosityNN : 0ℚ ≤ nu

      localEDBudgetPaid :
        (output : Z3.FourierMode) →
        let
          module P = Pay.LiveRegionPayment physicalSystem S output
          payment = paymentAt output (receiptsAt output)
        in
        P.deepBudget payment + P.coreEDBudget payment
        ≤ coefficient * localED output

  open UniformAnalyticReceipts public

  physicalCriticalRegionUniformFamily :
    UniformAnalyticReceipts →
    U.UniformPhysicalCriticalRegionFamily
  physicalCriticalRegionUniformFamily receipts = record
    { U.paymentAt = λ output → paymentAt output (receiptsAt receipts output)
    ; U.thetaStrictlyBelowOne =
        thetaStrictlyBelowOne (receiptsAt receipts
          Z3.zeroMode)
    ; U.coefficientNN = coefficientNN receipts
    ; U.viscosityNN = viscosityNN receipts
    ; U.thetaMeaning = λ output → refl
    ; U.localED = localED
    ; U.localEDMeaning = λ output → refl
    ; U.localEDBudgetPaid = localEDBudgetPaid receipts
    }

------------------------------------------------------------------------
-- The compiler seam itself is now closed.  The only remaining inhabitants
-- are exactly the analytic receipts carried by PerOutputAnalyticReceipts.
------------------------------------------------------------------------

uniformPhysicalCriticalRegionFamilyCompilerClosed : Bool
uniformPhysicalCriticalRegionFamilyCompilerClosed = true

uniformPhysicalCriticalRegionFamilyIntroducesPostulate : Bool
uniformPhysicalCriticalRegionFamilyIntroducesPostulate = false

uniformPhysicalCriticalRegionFamilyAnalyticReceiptsInhabitedHere : Bool
uniformPhysicalCriticalRegionFamilyAnalyticReceiptsInhabitedHere = false

clayPromotion : Bool
clayPromotion = false

uniformPhysicalCriticalRegionFamilyCompilerClosedIsTrue :
  uniformPhysicalCriticalRegionFamilyCompilerClosed ≡ true
uniformPhysicalCriticalRegionFamilyCompilerClosedIsTrue = refl
