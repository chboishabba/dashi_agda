{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650ThreeClassW2PaymentRound767Exact where

------------------------------------------------------------------------
-- ROUND767 / W2 IS EXACTLY THE INTEGRATED THREE-CLASS RESIDUAL PAYMENT
--
-- R766:
--
--   ThreeClassIntegral = 2 * R746Residual.
--
-- Since 2 > 0 over the rational carrier,
--
--   0 <= ThreeClassIntegral
--     iff
--   0 <= R746Residual.
--
-- R747 already proves
--
--   W2 iff 0 <= R746Residual.
--
-- Therefore W2 is exactly equivalent to ONE integrated three-channel payment:
--
--   0 <= integral [
--          2 LH_pair + CC_pair + HH_pair
--          + 6 (2 nu-delta) d_N
--        ] dt,
--   delta > 0.
--
-- This introduces no new analytic estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNR650OrbitAlignedW2PaymentRound747Exact as R747
import DASHI.Physics.Closure.NSTriadKNR650IntegratedThreeClassW2Round766Exact as R766

F : C3.RealField _
F = Rational.rationalRealField

twoPositive767 : 0ℚ < Fold.two
twoPositive767 = ℚP.positive⁻¹ Fold.two

module ThreeClassPayment
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf :
      (Time → ℚ) → (Time → ℚ) → Set)
    (projectedCross :
      R426.ProjectedCrossDerivativeCalculus Time VectorDerivativeOf)
    (vectorAlgebra :
      R425.VectorDerivativeAlgebra Time VectorDerivativeOf)
    (zeroCalculus :
      Endpoint.VectorZeroDerivative Time VectorDerivativeOf)
    (hermitianCalculus :
      R417.HermitianDerivativeCalculus
        Time VectorDerivativeOf ScalarDerivativeOf)
    (constantScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (scalarDerivativeAlgebra :
      R412.ScalarDerivativeAlgebra Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (integrationTransport :
      R495.IntegrationTransportAuthority Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf)
    (C :
      ModeCarrier.LiteralModeCarrier.LiteralCutoffModeCarrier
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D))
    (R :
      R405.LiteralCutoffSupport.LiteralNonzeroCutoffTrajectory
        Time initialTime integrateTo VectorDerivativeOf
        (R408.LiteralDynamics.literalPhysicalTrajectory
          Time initialTime integrateTo VectorDerivativeOf D)) where

  module Integrated = R766.IntegratedThreeClass
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Residual = R747.ResidualPayment
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module W2 = Residual.W2
  module Packet = Integrated.Packet

  record IntegratedThreeClassResidualPayment
      (cutoff : Nat)
      (terminal : Time) : Set₁ where
    field
      structure :
        Packet.LivePhysicalPacketStructure D C cutoff

      retainedMargin : ℚ
      retainedMarginPositive : 0ℚ < retainedMargin

      integratedThreeClassNonnegative :
        0ℚ ≤
        Integrated.integratedThreeClassResidual
          cutoff structure retainedMargin terminal

  open IntegratedThreeClassResidualPayment public

  r747BuildsThreeClassPayment :
    (cutoff : Nat) (terminal : Time) →
    Residual.OrbitAlignedResidualPayment cutoff terminal →
    IntegratedThreeClassResidualPayment cutoff terminal
  r747BuildsThreeClassPayment cutoff terminal P = record
    { structure = Residual.structure P
    ; retainedMargin = Residual.retainedMargin P
    ; retainedMarginPositive = Residual.retainedMarginPositive P
    ; integratedThreeClassNonnegative = paid
    }
    where
    S = Residual.structure P
    margin = Residual.retainedMargin P
    residual =
      Residual.G.integratedOrbitAlignedResidual cutoff margin terminal
    threeClass =
      Integrated.integratedThreeClassResidual cutoff S margin terminal

    scaledNonnegative :
      0ℚ ≤ Fold.two * residual
    scaledNonnegative =
      let
        h = Residual.integratedResidualNonnegative P
        doubled :
          0ℚ + 0ℚ ≤ residual + residual
        doubled = ℚP.+-mono-≤ h h
      in
      subst
        (0ℚ ≤_)
        (solve (Fold.two ∷ residual ∷ []))
        (subst
          (_≤ residual + residual)
          (solve [])
          doubled)

    paid : 0ℚ ≤ threeClass
    paid =
      subst
        (0ℚ ≤_)
        (sym
          (Integrated.integratedThreeClassResidualIsTwiceR746
            cutoff S margin terminal))
        scaledNonnegative

  threeClassPaymentBuildsR747 :
    (cutoff : Nat) (terminal : Time) →
    IntegratedThreeClassResidualPayment cutoff terminal →
    Residual.OrbitAlignedResidualPayment cutoff terminal
  threeClassPaymentBuildsR747 cutoff terminal P = record
    { Residual.structure = structure P
    ; Residual.retainedMargin = retainedMargin P
    ; Residual.retainedMarginPositive = retainedMarginPositive P
    ; Residual.integratedResidualNonnegative = paid
    }
    where
    S = structure P
    margin = retainedMargin P
    residual =
      Residual.G.integratedOrbitAlignedResidual cutoff margin terminal

    scaledNonnegative :
      0ℚ ≤ Fold.two * residual
    scaledNonnegative =
      subst
        (0ℚ ≤_)
        (Integrated.integratedThreeClassResidualIsTwiceR746
          cutoff S margin terminal)
        (integratedThreeClassNonnegative P)

    normalized :
      Fold.two * 0ℚ ≤ Fold.two * residual
    normalized =
      subst
        (_≤ Fold.two * residual)
        (solve [])
        scaledNonnegative

    paid : 0ℚ ≤ residual
    paid =
      ℚP.*-cancelˡ-≤-pos
        Fold.two normalized

  r742BuildsThreeClassPayment :
    (cutoff : Nat) (terminal : Time) →
    W2.IntegratedPhysicalPacketCombinedPayment cutoff terminal →
    IntegratedThreeClassResidualPayment cutoff terminal
  r742BuildsThreeClassPayment cutoff terminal P =
    r747BuildsThreeClassPayment cutoff terminal
      (Residual.r742BuildsOrbitAlignedResidualPayment
        cutoff terminal P)

  threeClassPaymentBuildsR742 :
    (cutoff : Nat) (terminal : Time) →
    IntegratedThreeClassResidualPayment cutoff terminal →
    W2.IntegratedPhysicalPacketCombinedPayment cutoff terminal
  threeClassPaymentBuildsR742 cutoff terminal P =
    Residual.orbitAlignedResidualPaymentBuildsR742
      cutoff terminal
      (threeClassPaymentBuildsR747 cutoff terminal P)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round767ThreeClassPaymentExactlyEquivalentToR747 : Bool
round767ThreeClassPaymentExactlyEquivalentToR747 = true

round767ThreeClassPaymentExactlyEquivalentToW2 : Bool
round767ThreeClassPaymentExactlyEquivalentToW2 = true

round767PreferredW2HasThreeIndependentTriadicChannels : Bool
round767PreferredW2HasThreeIndependentTriadicChannels = true

round767IndependentLHHLLeaves : Bool
round767IndependentLHHLLeaves = false

round767IntroducesEstimate : Bool
round767IntroducesEstimate = false

round767IntegratedThreeClassPaymentClosed : Bool
round767IntegratedThreeClassPaymentClosed = false

round767ClayPromotion : Bool
round767ClayPromotion = false

round767ThreeClassPaymentExactlyEquivalentToR747IsTrue :
  round767ThreeClassPaymentExactlyEquivalentToR747 ≡ true
round767ThreeClassPaymentExactlyEquivalentToR747IsTrue = refl

round767ThreeClassPaymentExactlyEquivalentToW2IsTrue :
  round767ThreeClassPaymentExactlyEquivalentToW2 ≡ true
round767ThreeClassPaymentExactlyEquivalentToW2IsTrue = refl

round767PreferredW2HasThreeIndependentTriadicChannelsIsTrue :
  round767PreferredW2HasThreeIndependentTriadicChannels ≡ true
round767PreferredW2HasThreeIndependentTriadicChannelsIsTrue = refl

round767IndependentLHHLLeavesIsFalse :
  round767IndependentLHHLLeaves ≡ false
round767IndependentLHHLLeavesIsFalse = refl

round767IntroducesEstimateIsFalse :
  round767IntroducesEstimate ≡ false
round767IntroducesEstimateIsFalse = refl

round767IntegratedThreeClassPaymentClosedIsFalse :
  round767IntegratedThreeClassPaymentClosed ≡ false
round767IntegratedThreeClassPaymentClosedIsFalse = refl

round767ClayPromotionIsFalse :
  round767ClayPromotion ≡ false
round767ClayPromotionIsFalse = refl
