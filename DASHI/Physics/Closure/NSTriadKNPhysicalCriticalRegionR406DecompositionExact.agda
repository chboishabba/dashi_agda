module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406DecompositionExact where

------------------------------------------------------------------------
-- S2b2d1b2 / NATIVE R236 PAYMENTS -> R432 SAME-OBJECT DECOMPOSITION
--
-- The only non-recursive input retained here is the literal R406 same-object
-- equality itself.  Once a producer identifies the global weighted remainder
-- with four times the sum of the live fixed-output coherent covariances, this
-- file constructs R432.FixedOutputRemainderDecomposition definitionally from
-- the corresponding physical critical-region payments.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact as Pay
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionToR432Exact as ToR432
import DASHI.Physics.Closure.NSTriadKNFixedOutputSignedCrossAggregationRound432Exact as R432
import DASHI.Physics.Closure.NSTriadKNHeatFactorizedPairRemainderRound299Exact as R299

F : C3.RealField _
F = Rational.rationalRealField

module Decomposition
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Live = LiveOwner.Live physicalSystem S

  PaymentAt : Z3.FourierMode → Set
  PaymentAt output =
    let module P = Pay.LiveRegionPayment physicalSystem S output
    in P.PhysicalCriticalRegionPayment

  paymentsFor :
    ((output : Z3.FourierMode) → PaymentAt output) →
    List Z3.FourierMode →
    List R432.FixedOutputSignedCrossPayment
  paymentsFor paymentAt [] = []
  paymentsFor paymentAt (output ∷ rest) =
    let module T = ToR432.ToR432 physicalSystem S output
    in
    T.criticalRegionPaymentToR432 (paymentAt output)
      ∷ paymentsFor paymentAt rest

  sumCovariance : List Z3.FourierMode → ℚ
  sumCovariance [] = 0
  sumCovariance (output ∷ rest) =
    Live.coherentCovarianceNumerator output + sumCovariance rest

  paymentsSignedCrossMeaning :
    (paymentAt : (output : Z3.FourierMode) → PaymentAt output) →
    (outputs : List Z3.FourierMode) →
    R432.sumSignedCross (paymentsFor paymentAt outputs)
    ≡ sumCovariance outputs
  paymentsSignedCrossMeaning paymentAt [] = refl
  paymentsSignedCrossMeaning paymentAt (output ∷ rest)
    rewrite paymentsSignedCrossMeaning paymentAt rest = refl

  record LiteralR406SameObjectData
      (paymentAt : (output : Z3.FourierMode) → PaymentAt output) : Set where
    constructor literal-r406-same-object-data
    field
      outputs : List Z3.FourierMode
      globalWeightedRemainder : ℚ
      globalRemainderIsFourCovariances :
        globalWeightedRemainder
        ≡ R299.four * sumCovariance outputs

  open LiteralR406SameObjectData public

  criticalRegionPaymentsToR406Decomposition :
    (paymentAt : (output : Z3.FourierMode) → PaymentAt output) →
    LiteralR406SameObjectData paymentAt →
    R432.FixedOutputRemainderDecomposition
  criticalRegionPaymentsToR406Decomposition paymentAt same = record
    { R432.payments = paymentsFor paymentAt (outputs same)
    ; R432.globalWeightedRemainder = globalWeightedRemainder same
    ; R432.globalRemainderIsFourFibreCrosses =
        trans
          (globalRemainderIsFourCovariances same)
          (cong
            (R299.four *_)
            (sym (paymentsSignedCrossMeaning paymentAt (outputs same))))
    }
    where
    open import Relation.Binary.PropositionalEquality using (sym)

criticalRegionR406DecompositionCompilerClosed : Bool
criticalRegionR406DecompositionCompilerClosed = true

criticalRegionR406DecompositionIntroducesPostulate : Bool
criticalRegionR406DecompositionIntroducesPostulate = false

literalR406SameObjectEqualityInhabitedHere : Bool
literalR406SameObjectEqualityInhabitedHere = false

clayPromotion : Bool
clayPromotion = false

criticalRegionR406DecompositionCompilerClosedIsTrue :
  criticalRegionR406DecompositionCompilerClosed ≡ true
criticalRegionR406DecompositionCompilerClosedIsTrue = refl
