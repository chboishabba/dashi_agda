module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCenteredBonyPaymentLiveExact where

------------------------------------------------------------------------
-- S2b2d1b2 / INDEXED LIVE THREE-REGION PAYMENT
--
-- Parameterizing the module by the actual physical system, helical scalars
-- and fixed output makes the producer fields definitionally about the literal
-- globally-centered Bony vectors constructed on that output fibre.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; _<_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBonyLiveExact as BonyLive

F : C3.RealField _
F = Rational.rationalRealField

module LivePayment
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S
  module Exact = BonyLive.LiveBony physicalSystem S output
  module Split = Exact.Split

  record LiveCenteredBonyPayment : Set where
    constructor live-centered-bony-payment
    field
      farLowBudget highHighBudget : ℚ
      coreCompanionMass coreEDBudget theta : ℚ

      viscosityNN :
        0ℚ ≤ Field30.viscosity physicalSystem

      thetaNN : 0ℚ ≤ theta
      thetaStrictlyBelowOne : theta < 1

      farLowPaid :
        0ℚ - Split.farLowWork
        ≤ farLowBudget

      highHighPaid :
        0ℚ - Split.highHighWork
        ≤ highHighBudget

      criticalPaid :
        0ℚ - Split.comparableWork
        ≤ theta * coreCompanionMass + coreEDBudget

  open LiveCenteredBonyPayment public

  liveCenteredBonyBudget :
    LiveCenteredBonyPayment → ℚ
  liveCenteredBonyBudget P =
    Field30.viscosity physicalSystem *
      ( farLowBudget P
      + highHighBudget P
      + theta P * coreCompanionMass P
      + coreEDBudget P )

  liveCenteredBonyPaymentClosesFixedOutput :
    (P : LiveCenteredBonyPayment) →
    Live.coherentCovarianceNumerator output
    ≤ liveCenteredBonyBudget P
  liveCenteredBonyPaymentClosesFixedOutput P =
    let
      classBound :
        (0ℚ - Split.farLowWork)
          + ((0ℚ - Split.highHighWork)
            + (0ℚ - Split.comparableWork))
        ≤
        farLowBudget P
          + ( highHighBudget P
            + (theta P * coreCompanionMass P + coreEDBudget P))
      classBound =
        ℚP.+-mono-≤
          (farLowPaid P)
          (ℚP.+-mono-≤
            (highHighPaid P)
            (criticalPaid P))

      scaled :
        Field30.viscosity physicalSystem *
          ( (0ℚ - Split.farLowWork)
          + ((0ℚ - Split.highHighWork)
            + (0ℚ - Split.comparableWork)) )
        ≤
        Field30.viscosity physicalSystem *
          ( farLowBudget P
          + ( highHighBudget P
            + (theta P * coreCompanionMass P + coreEDBudget P)) )
      scaled =
        let instance nuNN = nonNegative (viscosityNN P)
        in
        ℚP.*-monoˡ-≤-nonNeg
          (Field30.viscosity physicalSystem)
          classBound

      endpoint :
        Field30.viscosity physicalSystem *
          ( farLowBudget P
          + ( highHighBudget P
            + (theta P * coreCompanionMass P + coreEDBudget P)) )
        ≡ liveCenteredBonyBudget P
      endpoint =
        solve
          ( Field30.viscosity physicalSystem
          ∷ farLowBudget P
          ∷ highHighBudget P
          ∷ theta P
          ∷ coreCompanionMass P
          ∷ coreEDBudget P
          ∷ [])
    in
    subst
      (_≤ liveCenteredBonyBudget P)
      (sym Exact.liveCovarianceIsThreeCenteredBonyWorks)
      (subst
        (λ upper →
          Field30.viscosity physicalSystem *
            ( (0ℚ - Split.farLowWork)
            + ((0ℚ - Split.highHighWork)
              + (0ℚ - Split.comparableWork)) )
          ≤ upper)
        endpoint
        scaled)

liveCenteredBonyPhysicalPaymentCompilerClosed : Bool
liveCenteredBonyPhysicalPaymentCompilerClosed = true

liveCenteredBonyFarLowProducerClosedHere : Bool
liveCenteredBonyFarLowProducerClosedHere = false

liveCenteredBonyHighHighProducerClosedHere : Bool
liveCenteredBonyHighHighProducerClosedHere = false

liveCenteredBonyCriticalProducerClosedHere : Bool
liveCenteredBonyCriticalProducerClosedHere = false

liveCenteredBonyCrossOutputCoherenceRequired : Bool
liveCenteredBonyCrossOutputCoherenceRequired = false

clayPromotion : Bool
clayPromotion = false

liveCenteredBonyPhysicalPaymentCompilerClosedIsTrue :
  liveCenteredBonyPhysicalPaymentCompilerClosed ≡ true
liveCenteredBonyPhysicalPaymentCompilerClosedIsTrue = refl
