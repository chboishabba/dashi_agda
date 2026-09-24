{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650C2CriticalEnergyGrowthNormalFormRound659Exact where

------------------------------------------------------------------------
-- ROUND659 / C2 = CRITICAL-ENERGY GROWTH + POSITIVE DISSIPATION MARGIN
--
-- R646 states the strict C2 surplus on the literal physical trajectory as
--
--   P_N(T) - (2 nu - delta) D_N(T).
--
-- The already-owned exact critical-energy identity, given the same standard
-- scalar calculus used throughout R639/R646, is
--
--   X_N(T) + 2 nu D_N(T) = X_N(0) + P_N(T).
--
-- Therefore, on the SAME literal trajectory,
--
--   P_N(T) - (2 nu - delta) D_N(T)
--     = X_N(T) - X_N(0) + delta D_N(T).
--
-- Hence R650 C2 is exactly equivalent to ONE payment
--
--   X_N(T) - X_N(0) + delta D_N(T)
--     <= integral R406_N,
--
-- with delta > 0.
--
-- This is a useful analytic normal form because it separates what C2 must
-- achieve from any particular collar/remote/commutator producer.  It is not a
-- new estimate and it does not make the energy endpoint favorable by fiat.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_)
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
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNOneCancellationPaysRemainderAndCriticalRound414Exact as R414
import DASHI.Physics.Closure.NSTriadKNLiteralStrictMarginRadialSurplusRound646Exact as R646
import DASHI.Physics.Closure.NSTriadKNStrictMarginProductionToPhysicalCriticalGapRound645Exact as R645

F : C3.RealField _
F = Rational.rationalRealField

module EnergyGrowth
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
  module Calc = Energy.LiteralCriticalEnergyCalculus
    Time initialTime integrateTo
    DerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity
  module Radial = R646.RadialSurplus
    Time initialTime integrateTo
    DerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity
  module Unified = R414.Unified
    Time initialTime integrateTo DerivativeOf
  module Strict = R645.StrictMargin
    Time initialTime integrateTo
    DerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity

  criticalEnergyGrowthWithMargin :
    Live.LiteralRHSTrajectoryData →
    Nat → ℚ → Time → ℚ
  criticalEnergyGrowthWithMargin D cutoff margin terminal =
    let T = Live.literalPhysicalTrajectory D in
    Obs.criticalEnergyAt T cutoff terminal
      - Obs.criticalEnergyAt T cutoff initialTime
      + margin * Obs.integratedCriticalDissipation T cutoff terminal

  literalStrictSurplusIsCriticalEnergyGrowthWithMargin :
    (D : Live.LiteralRHSTrajectoryData) →
    (C : Modes.LiteralCutoffModeCarrier
      (Live.literalPhysicalTrajectory D)) →
    (cutoff : Nat) →
    (margin : ℚ) →
    (terminal : Time) →
    let T = Live.literalPhysicalTrajectory D in
    Obs.integratedCriticalProduction T cutoff terminal
      - ((Fold.two * Live.physicalViscosity (Live.support D)) - margin)
          * Obs.integratedCriticalDissipation T cutoff terminal
    ≡ criticalEnergyGrowthWithMargin D cutoff margin terminal
  literalStrictSurplusIsCriticalEnergyGrowthWithMargin
      D C cutoff margin terminal =
    let
      T = Live.literalPhysicalTrajectory D
      xT = Obs.criticalEnergyAt T cutoff terminal
      x0 = Obs.criticalEnergyAt T cutoff initialTime
      diss = Obs.integratedCriticalDissipation T cutoff terminal
      prod = Obs.integratedCriticalProduction T cutoff terminal
      visc = Fold.two * Live.physicalViscosity (Live.support D)

      energy :
        xT + visc * diss ≡ x0 + prod
      energy =
        Calc.integratedLiteralCriticalEnergyIdentity
          D C cutoff terminal

      shifted :
        (xT + visc * diss) - x0 - (visc - margin) * diss
        ≡
        (x0 + prod) - x0 - (visc - margin) * diss
      shifted =
        cong
          (λ value → value - x0 - (visc - margin) * diss)
          energy

      rightNormal :
        (x0 + prod) - x0 - (visc - margin) * diss
        ≡ prod - (visc - margin) * diss
      rightNormal =
        solve (x0 ∷ prod ∷ visc ∷ margin ∷ diss ∷ [])

      leftNormal :
        (xT + visc * diss) - x0 - (visc - margin) * diss
        ≡ xT - x0 + margin * diss
      leftNormal =
        solve (xT ∷ x0 ∷ visc ∷ margin ∷ diss ∷ [])
    in
    trans
      (sym rightNormal)
      (trans
        (sym shifted)
        leftNormal)

  integratedRadialSurplusIsCriticalEnergyGrowthWithMargin :
    (D : Live.LiteralRHSTrajectoryData) →
    (C : Modes.LiteralCutoffModeCarrier
      (Live.literalPhysicalTrajectory D)) →
    (cutoff : Nat) →
    (margin : ℚ) →
    (terminal : Time) →
    Radial.integratedRadialSurplus D cutoff margin terminal
    ≡ criticalEnergyGrowthWithMargin D cutoff margin terminal
  integratedRadialSurplusIsCriticalEnergyGrowthWithMargin
      D C cutoff margin terminal =
    trans
      (sym
        (Radial.integratedLiteralStrictSurplusSameObject
          D cutoff margin terminal))
      (literalStrictSurplusIsCriticalEnergyGrowthWithMargin
        D C cutoff margin terminal)

  record CriticalEnergyGrowthMarginPayment
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

      criticalEnergyGrowthPaidByLiteralR406 :
        criticalEnergyGrowthWithMargin
          D cutoff retainedMargin terminal
        ≤ Unified.literalRemainderIntegral
            (Live.literalPhysicalTrajectory D) R cutoff terminal

  open CriticalEnergyGrowthMarginPayment public

  energyGrowthPaymentBuildsRadialSurplusPayment :
    ∀ {D C R cutoff terminal} →
    CriticalEnergyGrowthMarginPayment D C R cutoff terminal →
    Radial.RadialSurplusPayment D C R cutoff terminal
  energyGrowthPaymentBuildsRadialSurplusPayment
      {D} {C} {R} {cutoff} {terminal} P =
    record
      { Radial.retainedMargin = retainedMargin P
      ; Radial.retainedMarginPositive = retainedMarginPositive P
      ; Radial.radialSurplusPaidByLiteralR406 =
          subst
            (λ value →
              value
              ≤ Unified.literalRemainderIntegral
                  (Live.literalPhysicalTrajectory D) R cutoff terminal)
            (sym
              (integratedRadialSurplusIsCriticalEnergyGrowthWithMargin
                D C cutoff (retainedMargin P) terminal))
            (criticalEnergyGrowthPaidByLiteralR406 P)
      }

  energyGrowthPaymentBuildsStrictMarginC2 :
    ∀ {D C R cutoff terminal} →
    CriticalEnergyGrowthMarginPayment D C R cutoff terminal →
    Strict.StrictMarginPhysicalProductionData D C R cutoff terminal
  energyGrowthPaymentBuildsStrictMarginC2 P =
    Radial.radialSurplusPaymentBuildsStrictMarginC2
      (energyGrowthPaymentBuildsRadialSurplusPayment P)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round659C2StrictSurplusEqualsCriticalEnergyGrowthPlusMargin : Bool
round659C2StrictSurplusEqualsCriticalEnergyGrowthPlusMargin = true

round659RadialSurplusEqualsCriticalEnergyGrowthPlusMargin : Bool
round659RadialSurplusEqualsCriticalEnergyGrowthPlusMargin = true

round659EnergyGrowthMarginPaymentCompilesToC2 : Bool
round659EnergyGrowthMarginPaymentCompilesToC2 = true

round659EnergyGrowthMarginPaymentClosed : Bool
round659EnergyGrowthMarginPaymentClosed = false

round659IntroducesNewNSEstimate : Bool
round659IntroducesNewNSEstimate = false

round659IntroducesNewClayLeaf : Bool
round659IntroducesNewClayLeaf = false

round659C2Closed : Bool
round659C2Closed = false

round659ClayPromotion : Bool
round659ClayPromotion = false

round659C2StrictSurplusEqualsCriticalEnergyGrowthPlusMarginIsTrue :
  round659C2StrictSurplusEqualsCriticalEnergyGrowthPlusMargin ≡ true
round659C2StrictSurplusEqualsCriticalEnergyGrowthPlusMarginIsTrue = refl

round659RadialSurplusEqualsCriticalEnergyGrowthPlusMarginIsTrue :
  round659RadialSurplusEqualsCriticalEnergyGrowthPlusMargin ≡ true
round659RadialSurplusEqualsCriticalEnergyGrowthPlusMarginIsTrue = refl

round659EnergyGrowthMarginPaymentCompilesToC2IsTrue :
  round659EnergyGrowthMarginPaymentCompilesToC2 ≡ true
round659EnergyGrowthMarginPaymentCompilesToC2IsTrue = refl

round659EnergyGrowthMarginPaymentClosedIsFalse :
  round659EnergyGrowthMarginPaymentClosed ≡ false
round659EnergyGrowthMarginPaymentClosedIsFalse = refl

round659IntroducesNewNSEstimateIsFalse :
  round659IntroducesNewNSEstimate ≡ false
round659IntroducesNewNSEstimateIsFalse = refl

round659IntroducesNewClayLeafIsFalse :
  round659IntroducesNewClayLeaf ≡ false
round659IntroducesNewClayLeafIsFalse = refl

round659C2ClosedIsFalse :
  round659C2Closed ≡ false
round659C2ClosedIsFalse = refl

round659ClayPromotionIsFalse :
  round659ClayPromotion ≡ false
round659ClayPromotionIsFalse = refl
