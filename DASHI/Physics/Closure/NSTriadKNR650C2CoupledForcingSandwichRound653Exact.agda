{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650C2CoupledForcingSandwichRound653Exact where

------------------------------------------------------------------------
-- ROUND653 / C2 BIDI RECAST ON THE SHARED C1 FORCING CURRENCY
--
-- R648's exact C2 payment is
--
--   S_delta <= R406,
--
-- where S_delta is the integrated physical-packet strict surplus.
--
-- R652 proves on the same literal trajectory
--
--   4 F = 2 R406 + G + H,
--
-- where
--   F = integrated GlobalForcingFull,
--   G = integrated self-Gram,
--   H = integrated self-flux tangent.
--
-- Hence C2 is equivalent to
--
--   2 S_delta + G + H <= 4 F.
--
-- This is the useful analytic "sandwich" normal form:
--
--   2 S_delta + diagonal <= 4 F <= B(T).
--
-- The right inequality is C1.  The left inequality is exactly C2, not a third
-- analytic obligation.  This owner supplies both directions and then reuses
-- R648/R645 to compile the coupled payment back to the existing strict-margin
-- physical critical slice.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNSymmetricUnorderedOrderedOffDiagonalRound539Exact as R539
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNLiveIntegratedDiagonalReducedNormalFormRound557Exact as R557
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567
import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as R568
import DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact as R414
import DASHI.Physics.Closure.NSTriadKNStrictMarginProductionToPhysicalCriticalGapRound645Exact as R645
import DASHI.Physics.Closure.NSTriadKNLivePhysicalPacketStrictSurplusRound648Exact as R648
import DASHI.Physics.Closure.NSTriadKNR650C1R406DiagonalCouplingRound652Exact as R652

F : C3.RealField _
F = Rational.rationalRealField

twoPositive653 : 0ℚ < R539.two
twoPositive653 =
  ℚP.+-mono-<-<
    (ℚP.positive⁻¹ 1ℚ)
    (ℚP.positive⁻¹ 1ℚ)

module Sandwich
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus Time DerivativeOf ScalarDerivativeOf)
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (integrationTransport :
      R495.IntegrationTransportAuthority Time integrateTo) where

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Modes = ModeCarrier.LiteralModeCarrier
    Time initialTime integrateTo DerivativeOf
  module Packet = R648.LivePacketSurplus
    Time initialTime integrateTo
    DerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity
  module Diag = R557.LiveIntegrated
    Time initialTime integrateTo DerivativeOf integrationTransport
  module Comm = R568.LiveCommutatorOnly
    Time initialTime integrateTo DerivativeOf integrationTransport
  module Shared = R652.Coupling
    Time initialTime integrateTo DerivativeOf integrationTransport
  module Unified = R414.Unified
    Time initialTime integrateTo DerivativeOf
  module Strict = R645.StrictMargin
    Time initialTime integrateTo
    DerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity

  record CoupledPhysicalPacketPayment
      (D : Live.LiteralRHSTrajectoryData)
      (C : Modes.LiteralCutoffModeCarrier
        (Live.literalPhysicalTrajectory D))
      (R : Support.LiteralNonzeroCutoffTrajectory
        (Live.literalPhysicalTrajectory D))
      (cutoff : Nat)
      (terminal : Time) : Set₁ where
    field
      structure : Packet.LivePhysicalPacketStructure D C cutoff

      retainedMargin : ℚ
      retainedMarginPositive : 0ℚ < retainedMargin

      coupledPacketDiagonalBelowC1 :
        R539.two *
          Packet.integratedPhysicalPacketStrictSurplus
            D cutoff retainedMargin terminal
          + integrateTo
              (Diag.selfGram
                (Live.literalPhysicalTrajectory D) R cutoff)
              terminal
          + integrateTo
              (Diag.selfFluxTangent
                (Live.literalPhysicalTrajectory D) R cutoff)
              terminal
        ≤
        R567.four567 *
          Comm.integratedGlobalForcingFull
            (Live.literalPhysicalTrajectory D) R cutoff terminal

  open CoupledPhysicalPacketPayment public

  coupledPaymentBuildsR648 :
    ∀ {D C R cutoff terminal} →
    CoupledPhysicalPacketPayment D C R cutoff terminal →
    Packet.PhysicalPacketSurplusPayment D C R cutoff terminal
  coupledPaymentBuildsR648
      {D} {C} {R} {cutoff} {terminal} P =
    record
      { Packet.structure = structure P
      ; Packet.retainedMargin = retainedMargin P
      ; Packet.retainedMarginPositive = retainedMarginPositive P
      ; Packet.physicalPacketSurplusPaidByLiteralR406 = paid
      }
    where
    T = Live.literalPhysicalTrajectory D
    margin = retainedMargin P

    surplus =
      Packet.integratedPhysicalPacketStrictSurplus
        D cutoff margin terminal

    remainder =
      Unified.literalRemainderIntegral T R cutoff terminal

    gram =
      integrateTo (Diag.selfGram T R cutoff) terminal

    tangent =
      integrateTo (Diag.selfFluxTangent T R cutoff) terminal

    forcing =
      R567.four567 *
        Comm.integratedGlobalForcingFull T R cutoff terminal

    forcingExact :
      forcing ≡ R539.two * remainder + gram + tangent
    forcingExact =
      Shared.integratedFourForcingIsTwoR406PlusDiagonal
        T R cutoff terminal

    withSharedRemainder :
      R539.two * surplus + gram + tangent
      ≤ R539.two * remainder + gram + tangent
    withSharedRemainder =
      subst
        (λ right →
          R539.two * surplus + gram + tangent ≤ right)
        forcingExact
        (coupledPacketDiagonalBelowC1 P)

    commonDiagonalCancelled :
      R539.two * surplus ≤ R539.two * remainder
    commonDiagonalCancelled =
      let
        normalized :
          R539.two * surplus + (gram + tangent)
          ≤ R539.two * remainder + (gram + tangent)
        normalized =
          subst
            (λ left →
              left ≤ R539.two * remainder + (gram + tangent))
            (solve (R539.two * surplus ∷ gram ∷ tangent ∷ []))
            (subst
              (λ right →
                R539.two * surplus + gram + tangent ≤ right)
              (solve (R539.two * remainder ∷ gram ∷ tangent ∷ []))
              withSharedRemainder)
      in
      ℚP.+-cancelʳ-≤ (gram + tangent) normalized

    paid : surplus ≤ remainder
    paid =
      ℚP.*-cancelˡ-≤-pos R539.two commonDiagonalCancelled

  r648PaymentBuildsCoupled :
    ∀ {D C R cutoff terminal} →
    Packet.PhysicalPacketSurplusPayment D C R cutoff terminal →
    CoupledPhysicalPacketPayment D C R cutoff terminal
  r648PaymentBuildsCoupled
      {D} {C} {R} {cutoff} {terminal} P =
    record
      { structure = Packet.structure P
      ; retainedMargin = Packet.retainedMargin P
      ; retainedMarginPositive = Packet.retainedMarginPositive P
      ; coupledPacketDiagonalBelowC1 = coupled
      }
    where
    T = Live.literalPhysicalTrajectory D
    margin = Packet.retainedMargin P

    surplus =
      Packet.integratedPhysicalPacketStrictSurplus
        D cutoff margin terminal

    remainder =
      Unified.literalRemainderIntegral T R cutoff terminal

    gram =
      integrateTo (Diag.selfGram T R cutoff) terminal

    tangent =
      integrateTo (Diag.selfFluxTangent T R cutoff) terminal

    forcing =
      R567.four567 *
        Comm.integratedGlobalForcingFull T R cutoff terminal

    doubled :
      R539.two * surplus ≤ R539.two * remainder
    doubled =
      subst
        (λ left → left ≤ R539.two * remainder)
        (solve (surplus ∷ []))
        (subst
          (λ right → surplus + surplus ≤ right)
          (solve (remainder ∷ []))
          (ℚP.+-mono-≤
            (Packet.physicalPacketSurplusPaidByLiteralR406 P)
            (Packet.physicalPacketSurplusPaidByLiteralR406 P)))

    withDiagonal :
      R539.two * surplus + gram + tangent
      ≤ R539.two * remainder + gram + tangent
    withDiagonal =
      ℚP.+-mono-≤
        (ℚP.+-mono-≤ doubled ℚP.≤-refl)
        ℚP.≤-refl

    forcingExact :
      forcing ≡ R539.two * remainder + gram + tangent
    forcingExact =
      Shared.integratedFourForcingIsTwoR406PlusDiagonal
        T R cutoff terminal

    coupled :
      R539.two * surplus + gram + tangent ≤ forcing
    coupled =
      subst
        (λ right →
          R539.two * surplus + gram + tangent ≤ right)
        (sym forcingExact)
        withDiagonal

  coupledPaymentBuildsStrictMarginC2 :
    ∀ {D C R cutoff terminal} →
    CoupledPhysicalPacketPayment D C R cutoff terminal →
    Strict.StrictMarginPhysicalProductionData D C R cutoff terminal
  coupledPaymentBuildsStrictMarginC2 P =
    Packet.physicalPacketPaymentBuildsStrictMarginC2
      (coupledPaymentBuildsR648 P)

------------------------------------------------------------------------
-- Status / analytic interpretation.
------------------------------------------------------------------------

round653CoupledSandwichToR648Closed : Bool
round653CoupledSandwichToR648Closed = true

round653R648ToCoupledSandwichClosed : Bool
round653R648ToCoupledSandwichClosed = true

round653CoupledSandwichExactlyEquivalentToC2 : Bool
round653CoupledSandwichExactlyEquivalentToC2 = true

round653C1AndC2CanBeSearchedAsLiteralSandwich : Bool
round653C1AndC2CanBeSearchedAsLiteralSandwich = true

round653IntroducesThirdAnalyticLeaf : Bool
round653IntroducesThirdAnalyticLeaf = false

round653C1Closed : Bool
round653C1Closed = false

round653C2Closed : Bool
round653C2Closed = false

round653ClayPromotion : Bool
round653ClayPromotion = false

round653CoupledSandwichToR648ClosedIsTrue :
  round653CoupledSandwichToR648Closed ≡ true
round653CoupledSandwichToR648ClosedIsTrue = refl

round653R648ToCoupledSandwichClosedIsTrue :
  round653R648ToCoupledSandwichClosed ≡ true
round653R648ToCoupledSandwichClosedIsTrue = refl

round653CoupledSandwichExactlyEquivalentToC2IsTrue :
  round653CoupledSandwichExactlyEquivalentToC2 ≡ true
round653CoupledSandwichExactlyEquivalentToC2IsTrue = refl

round653C1AndC2CanBeSearchedAsLiteralSandwichIsTrue :
  round653C1AndC2CanBeSearchedAsLiteralSandwich ≡ true
round653C1AndC2CanBeSearchedAsLiteralSandwichIsTrue = refl

round653IntroducesThirdAnalyticLeafIsFalse :
  round653IntroducesThirdAnalyticLeaf ≡ false
round653IntroducesThirdAnalyticLeafIsFalse = refl

round653C1ClosedIsFalse : round653C1Closed ≡ false
round653C1ClosedIsFalse = refl

round653C2ClosedIsFalse : round653C2Closed ≡ false
round653C2ClosedIsFalse = refl

round653ClayPromotionIsFalse :
  round653ClayPromotion ≡ false
round653ClayPromotionIsFalse = refl
