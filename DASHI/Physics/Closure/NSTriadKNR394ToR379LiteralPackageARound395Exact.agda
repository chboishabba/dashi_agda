module DASHI.Physics.Closure.NSTriadKNR394ToR379LiteralPackageARound395Exact where

------------------------------------------------------------------------
-- ROUND395 / R394 LITERAL TEMPORAL PAYMENT -> R379 PACKAGE A
--
-- R394 already constructs the actual R303 payment with
--
--   signedGramIntegral = Integral(literal R378 global Gram debt)
--
-- definitionally.  R379 still exposed one obsolete caller socket asserting
-- afterwards that this scalar equals the physical `integrateTo` of its literal
-- R378 debt.  This module removes that duplicate authority.
--
-- A temporal realization is required to identify its debt pointwise with the
-- R379 physical debt and its interval Integral with the physical `integrateTo`.
-- R393 integral congruence then derives the old R379 equality.  The caller
-- cannot choose an unrelated R303 scalar.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _≤_)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNSignedGramFluxPaymentRound303Exact as R303
import DASHI.Physics.Closure.NSTriadKNSignedIntegratedGramConsumerRound293Exact as R293
import DASHI.Physics.Closure.NSTriadKNPhysicalGlobalGramToPackageARound379Exact as R379
import DASHI.Physics.Closure.NSTriadKNLiteralR378TemporalIntegrationBoundaryRound393Exact as R393
import DASHI.Physics.Closure.NSTriadKNLiteralR378ToR303PaymentRound394Exact as R394

F : C3.RealField _
F = Rational.rationalRealField

module LiteralTemporalPackageA
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module G = R379.PhysicalGlobalGramToPackageA
    Time initialTime integrateTo DerivativeOf
  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf

  record LiteralTemporalPackageAInputs
      (T : Dyn.PhysicalNSGalerkinTrajectory) : Set₁ where
    field
      energyDissipation : Nat → Time → ℚ

      integrationMonotone :
        (left right : Time → ℚ) →
        ((t : Time) → left t ≤ right t) →
        (terminal : Time) →
        integrateTo left terminal ≤ integrateTo right terminal

      integrationAdditive :
        (left right : Time → ℚ) →
        (terminal : Time) →
        integrateTo (λ time → left time + right time) terminal
        ≡ integrateTo left terminal + integrateTo right terminal

      globalCellMassBound :
        (N : Nat) (t : Time) →
        G.physicalGlobalCellMass T N t
        ≤ R293.thirtySix * energyDissipation N t

      scaledEnergyIntegralUpperBound : Time → ℚ
      integratedScaledEnergyBound :
        (N : Nat) (terminal : Time) →
        integrateTo
          (λ time → R293.thirtySix * energyDissipation N time)
          terminal
        ≤ scaledEnergyIntegralUpperBound terminal

      temporal :
        (N : Nat) (terminal : Time) →
        R393.LiteralR378TemporalRealization Time

      temporalInitialIsPhysicalInitial :
        (N : Nat) (terminal : Time) →
        R393.initialTime (temporal N terminal) ≡ initialTime

      temporalFinalIsRequestedTerminal :
        (N : Nat) (terminal : Time) →
        R393.finalTime (temporal N terminal) ≡ terminal

      temporalDebtIsLiteralPhysicalDebt :
        (N : Nat) (terminal t : Time) →
        R393.literalGlobalGramDebt (temporal N terminal) t
        ≡ G.physicalGlobalGramDebt T N t

      temporalIntegralIsPhysicalIntegration :
        (N : Nat) (terminal : Time) (f : Time → ℚ) →
        R393.Integral (temporal N terminal) f
        ≡ integrateTo f terminal

      paymentLeaves :
        (N : Nat) (terminal : Time) →
        R394.LiteralR378PaymentLeaves (temporal N terminal)

      signedGramIntegralUpperBound : Time → ℚ

      literalPaymentPaidUniformlyInCutoff :
        (N : Nat) (terminal : Time) →
        R303.signedGramUpperBound
          (R394.literalR378ToR303Payment
            (temporal N terminal) (paymentLeaves N terminal))
        ≤ signedGramIntegralUpperBound terminal

  open LiteralTemporalPackageAInputs public

  literalPayment :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    LiteralTemporalPackageAInputs T →
    Nat → Time → R303.SignedGramFluxPayment
  literalPayment T I N terminal =
    R394.literalR378ToR303Payment
      (temporal I N terminal)
      (paymentLeaves I N terminal)

  literalPaymentIsSameIntegratedPhysicalDebt :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (I : LiteralTemporalPackageAInputs T) →
    (N : Nat) (terminal : Time) →
    R303.signedGramIntegral (literalPayment T I N terminal)
    ≡ integrateTo (G.physicalGlobalGramDebt T N) terminal
  literalPaymentIsSameIntegratedPhysicalDebt T I N terminal =
    let
      R = temporal I N terminal
      pointwise :
        (t : Time) →
        R393.literalGlobalGramDebt R t
        ≡ G.physicalGlobalGramDebt T N t
      pointwise = temporalDebtIsLiteralPhysicalDebt I N terminal
    in
    trans
      (R394.literalR378SignedIntegralIsDefinitionallyR303Integral
        R (paymentLeaves I N terminal))
      (trans
        (R393.integralCongruence R pointwise)
        (temporalIntegralIsPhysicalIntegration I N terminal
          (G.physicalGlobalGramDebt T N)))

  asR379Inputs :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (I : LiteralTemporalPackageAInputs T) →
    G.PhysicalGlobalSignedGramInputs T
  asR379Inputs T I = record
    { G.energyDissipation = energyDissipation I
    ; G.integrationMonotone = integrationMonotone I
    ; G.integrationAdditive = integrationAdditive I
    ; G.globalCellMassBound = globalCellMassBound I
    ; G.scaledEnergyIntegralUpperBound = scaledEnergyIntegralUpperBound I
    ; G.integratedScaledEnergyBound = integratedScaledEnergyBound I
    ; G.gramFluxPayment = literalPayment T I
    ; G.gramFluxIsSameIntegratedGlobalDebt =
        literalPaymentIsSameIntegratedPhysicalDebt T I
    ; G.signedGramIntegralUpperBound = signedGramIntegralUpperBound I
    ; G.gramFluxPaidUniformlyInCutoff = literalPaymentPaidUniformlyInCutoff I
    }

  literalTemporalR378PaymentBuildsPackageA :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    LiteralTemporalPackageAInputs T →
    Dyn.PhysicalNSMixedHelicitySpacetimeBudget T
  literalTemporalR378PaymentBuildsPackageA T I =
    G.physicalGlobalSignedGramBuildsPackageA T (asR379Inputs T I)

round395CallerSuppliesR379SameIntegralEquality : Bool
round395CallerSuppliesR379SameIntegralEquality = false

round395R303PaymentIsConstructedFromLiteralR378TemporalObject : Bool
round395R303PaymentIsConstructedFromLiteralR378TemporalObject = true

round395LiteralTemporalPaymentBuildsR240PackageA : Bool
round395LiteralTemporalPaymentBuildsR240PackageA = true

round395ActualTemporalFTCProducerRecovered : Bool
round395ActualTemporalFTCProducerRecovered = false

round395CallerSuppliesR379SameIntegralEqualityIsFalse :
  round395CallerSuppliesR379SameIntegralEquality ≡ false
round395CallerSuppliesR379SameIntegralEqualityIsFalse = refl

round395R303PaymentIsConstructedFromLiteralR378TemporalObjectIsTrue :
  round395R303PaymentIsConstructedFromLiteralR378TemporalObject ≡ true
round395R303PaymentIsConstructedFromLiteralR378TemporalObjectIsTrue = refl
