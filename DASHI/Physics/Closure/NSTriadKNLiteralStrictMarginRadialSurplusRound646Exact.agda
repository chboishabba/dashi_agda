{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNLiteralStrictMarginRadialSurplusRound646Exact where

------------------------------------------------------------------------
-- ROUND646 / LITERAL STRICT-MARGIN SURPLUS -> RADIAL WEIGHTED TRANSFER
--
-- R645 shows that the preferred C2 theorem is
--
--   P_N(T) <= (2*nu-delta_N) D_N(T) + integral R406_N,
--   delta_N > 0.
--
-- The literal production already has an exact same-object representation:
--
--   criticalProductionRate
--     = 2 * radialWeightedTransfer
--
-- on the SAME finite Galerkin system (R104 radial-order carrier).
--
-- This owner therefore defines the exact signed surplus rate
--
--   S_N^delta(t)
--     = 2*radialWeightedTransfer_N(t)
--       - (2*nu-delta) criticalDissipationRate_N(t),
--
-- proves that its spacetime integral is exactly
--
--   P_N(T) - (2*nu-delta) D_N(T),
--
-- and compiles ONE quantitative payment
--
--   integral S_N^delta <= integral R406_N
--
-- directly into R645's strict-margin C2 record.  Thus the remaining nonlinear
-- theorem can be searched/proved on the normalized radial carrier without
-- changing the Clay-facing statement.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_; -_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans; subst)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffModeCarrierExact as ModeCarrier
import DASHI.Physics.Closure.NSTriadKNFixedOutputFluxFiniteDerivativeCompilerRound412Exact as R412
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionRadialOrderExact as Radial
import DASHI.Physics.Closure.NSTriadKNCriticalProductionPacketLayerCakeRound104Exact as LayerCake
import DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact as R414
import DASHI.Physics.Closure.NSTriadKNStrictMarginProductionToPhysicalCriticalGapRound645Exact as R645

F : C3.RealField _
F = Rational.rationalRealField

module RadialSurplus
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
      Energy.ScalarIntegrationLinearity Time integrateTo) where

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Modes = ModeCarrier.LiteralModeCarrier
    Time initialTime integrateTo DerivativeOf
  module Obs = Fold.LiteralCriticalObservables
    Time initialTime integrateTo DerivativeOf
  module Unified = R414.Unified
    Time initialTime integrateTo DerivativeOf
  module Strict = R645.StrictMargin
    Time initialTime integrateTo
    DerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity

  radialProductionRate :
    Live.LiteralRHSTrajectoryData → Nat → Time → ℚ
  radialProductionRate D cutoff time =
    let system =
          Live.Base.systemAt
            (Live.stateTrajectory (Live.support D)) cutoff time
    in
    Fold.two *
      LayerCake.weightedTransfer
        (Radial.radialBandTransfers system (Audit.modes system))

  productionRateIsRadialProductionRate :
    (D : Live.LiteralRHSTrajectoryData) →
    (cutoff : Nat) (time : Time) →
    Obs.productionRateAt
      (Live.literalPhysicalTrajectory D) cutoff time
    ≡ radialProductionRate D cutoff time
  productionRateIsRadialProductionRate D cutoff time =
    Radial.literalCriticalProductionIsTwiceRadialWeightedTransfer
      (Live.Base.systemAt
        (Live.stateTrajectory (Live.support D)) cutoff time)

  strictRadialSurplusRate :
    Live.LiteralRHSTrajectoryData →
    Nat → ℚ → Time → ℚ
  strictRadialSurplusRate D cutoff margin time =
    radialProductionRate D cutoff time
      - ((Fold.two * Live.physicalViscosity (Live.support D)) - margin)
          * Obs.dissipationRateAt
              (Live.literalPhysicalTrajectory D) cutoff time

  literalStrictSurplusRateSameObject :
    (D : Live.LiteralRHSTrajectoryData) →
    (cutoff : Nat) (margin : ℚ) (time : Time) →
    Obs.productionRateAt
        (Live.literalPhysicalTrajectory D) cutoff time
      - ((Fold.two * Live.physicalViscosity (Live.support D)) - margin)
          * Obs.dissipationRateAt
              (Live.literalPhysicalTrajectory D) cutoff time
    ≡ strictRadialSurplusRate D cutoff margin time
  literalStrictSurplusRateSameObject D cutoff margin time
    rewrite productionRateIsRadialProductionRate D cutoff time = refl

  integratedRadialSurplus :
    Live.LiteralRHSTrajectoryData →
    Nat → ℚ → Time → ℚ
  integratedRadialSurplus D cutoff margin terminal =
    integrateTo (strictRadialSurplusRate D cutoff margin) terminal

  integratedLiteralStrictSurplusSameObject :
    (D : Live.LiteralRHSTrajectoryData) →
    (cutoff : Nat) (margin : ℚ) (terminal : Time) →
    Obs.integratedCriticalProduction
        (Live.literalPhysicalTrajectory D) cutoff terminal
      - ((Fold.two * Live.physicalViscosity (Live.support D)) - margin)
          * Obs.integratedCriticalDissipation
              (Live.literalPhysicalTrajectory D) cutoff terminal
    ≡ integratedRadialSurplus D cutoff margin terminal
  integratedLiteralStrictSurplusSameObject D cutoff margin terminal =
    let
      T = Live.literalPhysicalTrajectory D
      coefficient =
        (Fold.two * Live.physicalViscosity (Live.support D)) - margin

      production = Obs.productionRateAt T cutoff
      dissipation = Obs.dissipationRateAt T cutoff

      pointwise :
        (time : Time) →
        production time - coefficient * dissipation time
        ≡ strictRadialSurplusRate D cutoff margin time
      pointwise = literalStrictSurplusRateSameObject D cutoff margin

      congruent :
        integrateTo
          (λ time → production time - coefficient * dissipation time)
          terminal
        ≡ integratedRadialSurplus D cutoff margin terminal
      congruent =
        Energy.integrationCongruent integrationLinearity pointwise terminal

      additive :
        integrateTo
          (λ time → production time + (- coefficient) * dissipation time)
          terminal
        ≡ integrateTo production terminal
          + integrateTo
              (λ time → (- coefficient) * dissipation time)
              terminal
      additive =
        Energy.integrationAdditive integrationLinearity
          production
          (λ time → (- coefficient) * dissipation time)
          terminal

      scaled :
        integrateTo
          (λ time → (- coefficient) * dissipation time)
          terminal
        ≡ (- coefficient) * integrateTo dissipation terminal
      scaled =
        Energy.integrationConstantScale integrationLinearity
          (- coefficient) dissipation terminal

      split :
        integrateTo
          (λ time → production time - coefficient * dissipation time)
          terminal
        ≡
        Obs.integratedCriticalProduction T cutoff terminal
          - coefficient
              * Obs.integratedCriticalDissipation T cutoff terminal
      split =
        trans
          (Energy.integrationCongruent integrationLinearity
            (λ time → solve
              (production time ∷ coefficient ∷ dissipation time ∷ []))
            terminal)
          (trans additive
            (trans
              (cong
                (integrateTo production terminal +_)
                scaled)
              (solve
                ( integrateTo production terminal
                ∷ coefficient
                ∷ integrateTo dissipation terminal
                ∷ [] ))))
    in
    trans (sym split) congruent

  record RadialSurplusPayment
      (D : Live.LiteralRHSTrajectoryData)
      (C : Modes.LiteralCutoffModeCarrier
        (Live.literalPhysicalTrajectory D))
      (R : Support.LiteralNonzeroCutoffTrajectory
        (Live.literalPhysicalTrajectory D))
      (cutoff : Nat)
      (terminal : Time) : Set where
    field
      retainedMargin : ℚ
      retainedMarginPositive : 0ℚ < retainedMargin

      radialSurplusPaidByLiteralR406 :
        integratedRadialSurplus D cutoff retainedMargin terminal
        ≤ Unified.literalRemainderIntegral
            (Live.literalPhysicalTrajectory D) R cutoff terminal

  open RadialSurplusPayment public

  radialSurplusPaymentBuildsStrictMarginC2 :
    ∀ {D C R cutoff terminal} →
    RadialSurplusPayment D C R cutoff terminal →
    Strict.StrictMarginPhysicalProductionData D C R cutoff terminal
  radialSurplusPaymentBuildsStrictMarginC2 {D} {R = R} {cutoff} {terminal} P =
    record
      { Strict.retainedMargin = retainedMargin P
      ; Strict.retainedMarginPositive = retainedMarginPositive P
      ; Strict.strictMarginProductionEstimate =
          productionEstimate
      }
    where
    T = Live.literalPhysicalTrajectory D
    margin = retainedMargin P
    coefficient =
      (Fold.two * Live.physicalViscosity (Live.support D)) - margin
    remainder =
      Unified.literalRemainderIntegral T R cutoff terminal

    surplusBound :
      Obs.integratedCriticalProduction T cutoff terminal
        - coefficient
            * Obs.integratedCriticalDissipation T cutoff terminal
      ≤ remainder
    surplusBound =
      subst
        (λ value → value ≤ remainder)
        (sym
          (integratedLiteralStrictSurplusSameObject
            D cutoff margin terminal))
        (radialSurplusPaidByLiteralR406 P)

    shifted :
      (Obs.integratedCriticalProduction T cutoff terminal
        - coefficient
            * Obs.integratedCriticalDissipation T cutoff terminal)
        + coefficient
            * Obs.integratedCriticalDissipation T cutoff terminal
      ≤ remainder
        + coefficient
            * Obs.integratedCriticalDissipation T cutoff terminal
    shifted = ℚP.+-mono-≤ surplusBound ℚP.≤-refl

    productionEstimate :
      Obs.integratedCriticalProduction T cutoff terminal
      ≤ coefficient
          * Obs.integratedCriticalDissipation T cutoff terminal
        + remainder
    productionEstimate =
      subst
        (λ left →
          left
          ≤ coefficient
              * Obs.integratedCriticalDissipation T cutoff terminal
            + remainder)
        (solve
          ( Obs.integratedCriticalProduction T cutoff terminal
          ∷ coefficient
          ∷ Obs.integratedCriticalDissipation T cutoff terminal
          ∷ [] ))
        (subst
          (λ right →
            (Obs.integratedCriticalProduction T cutoff terminal
              - coefficient
                  * Obs.integratedCriticalDissipation T cutoff terminal)
              + coefficient
                  * Obs.integratedCriticalDissipation T cutoff terminal
            ≤ right)
          (solve
            ( remainder
            ∷ coefficient
            ∷ Obs.integratedCriticalDissipation T cutoff terminal
            ∷ [] ))
          shifted)

------------------------------------------------------------------------
-- Status / trust boundary.
------------------------------------------------------------------------

round646LiteralProductionToRadialWeightedTransferClosed : Bool
round646LiteralProductionToRadialWeightedTransferClosed = true

round646IntegratedStrictSurplusSameObjectClosed : Bool
round646IntegratedStrictSurplusSameObjectClosed = true

round646OneRadialSurplusPaymentCompilesToR645C2 : Bool
round646OneRadialSurplusPaymentCompilesToR645C2 = true

round646RemainingNonlinearLeafIsRadialSurplusPayment : Bool
round646RemainingNonlinearLeafIsRadialSurplusPayment = true

round646PacketLayerCakeRepresentationNeededForCompiler : Bool
round646PacketLayerCakeRepresentationNeededForCompiler = false

round646IntroducesNewNSEstimate : Bool
round646IntroducesNewNSEstimate = false

round646ClayPromotion : Bool
round646ClayPromotion = false

round646LiteralProductionToRadialWeightedTransferClosedIsTrue :
  round646LiteralProductionToRadialWeightedTransferClosed ≡ true
round646LiteralProductionToRadialWeightedTransferClosedIsTrue = refl

round646IntegratedStrictSurplusSameObjectClosedIsTrue :
  round646IntegratedStrictSurplusSameObjectClosed ≡ true
round646IntegratedStrictSurplusSameObjectClosedIsTrue = refl

round646OneRadialSurplusPaymentCompilesToR645C2IsTrue :
  round646OneRadialSurplusPaymentCompilesToR645C2 ≡ true
round646OneRadialSurplusPaymentCompilesToR645C2IsTrue = refl

round646RemainingNonlinearLeafIsRadialSurplusPaymentIsTrue :
  round646RemainingNonlinearLeafIsRadialSurplusPayment ≡ true
round646RemainingNonlinearLeafIsRadialSurplusPaymentIsTrue = refl

round646PacketLayerCakeRepresentationNeededForCompilerIsFalse :
  round646PacketLayerCakeRepresentationNeededForCompiler ≡ false
round646PacketLayerCakeRepresentationNeededForCompilerIsFalse = refl

round646IntroducesNewNSEstimateIsFalse :
  round646IntroducesNewNSEstimate ≡ false
round646IntroducesNewNSEstimateIsFalse = refl

round646ClayPromotionIsFalse :
  round646ClayPromotion ≡ false
round646ClayPromotionIsFalse = refl
