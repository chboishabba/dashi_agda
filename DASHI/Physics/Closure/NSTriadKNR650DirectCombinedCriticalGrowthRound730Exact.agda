{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650DirectCombinedCriticalGrowthRound730Exact where

------------------------------------------------------------------------
-- ROUND730 / COLLAPSE R726 + STRICT-MARGIN C2 DIRECTLY ONTO R723 CURRENCY
--
-- R659 gives the exact strict-margin C2 normal form
--
--   Growth_delta(N,T)
--     = X_N(T) - X_N(0) + delta D_N(T)
--     <= literalR406_N(T).
--
-- R726 isolates the one-sided transport
--
--   literalR406_N(T) <= IntegratedCombined_N(T).
--
-- Therefore B+C compose to the strictly smaller direct obligation
--
--   Growth_delta(N,T) <= IntegratedCombined_N(T).
--
-- This direct inequality is sufficient for the critical barrier together with
-- the R723 cutoff-uniform combined payment:
--
--   IntegratedCombined_N(T) <= 12 B(T)
--
-- implies
--
--   X_N(T) + delta D_N(T) <= X_N(0) + 12 B(T).
--
-- Crucially, the direct theorem does NOT require callers to separately prove
-- R406 transport or strict-margin production.  Those remain a sufficient
-- producer factorization of the direct theorem, not mandatory terminal leaves.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; _<_)
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
import DASHI.Physics.Closure.NSTriadKNR650C2CriticalEnergyGrowthNormalFormRound659Exact as R659
import DASHI.Physics.Closure.NSTriadKNR650CombinedSelfExternalSpacetimeRound723Exact as R723
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700
import DASHI.Physics.Closure.NSTriadKNR650CombinedToLiteralR406Round726Exact as R726

F : C3.RealField _
F = Rational.rationalRealField

module DirectCombinedGrowth
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

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf

  module Obs = Fold.LiteralCriticalObservables
    Time initialTime integrateTo VectorDerivativeOf

  module Growth = R659.EnergyGrowth
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity

  module Combined = R723.CombinedSpacetime
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus
    FTC integrationLinearity integrationTransport D

  module Bridge = R726.CombinedToR406
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus
    FTC integrationLinearity integrationTransport D

  T = Live.literalPhysicalTrajectory D

  record DirectCombinedCriticalGrowthPayment
      (cutoff : Nat)
      (terminal : Time) : Set where
    field
      retainedMargin : ℚ
      retainedMarginPositive : 0ℚ < retainedMargin

      criticalGrowthPaidByCombined :
        Growth.criticalEnergyGrowthWithMargin
          D cutoff retainedMargin terminal
        ≤ Combined.integratedCombinedSelfExternal cutoff terminal

  open DirectCombinedCriticalGrowthPayment public

  r726PlusC2BuildDirectCombinedGrowth :
    (cutoff : Nat) →
    (terminal : Time) →
    Bridge.CombinedR406Transport R →
    Growth.CriticalEnergyGrowthMarginPayment
      D C R cutoff terminal →
    DirectCombinedCriticalGrowthPayment cutoff terminal
  r726PlusC2BuildDirectCombinedGrowth cutoff terminal B P = record
    { retainedMargin = Growth.retainedMargin P
    ; retainedMarginPositive = Growth.retainedMarginPositive P
    ; criticalGrowthPaidByCombined =
        ℚP.≤-trans
          (Growth.criticalEnergyGrowthPaidByLiteralR406 P)
          (Bridge.literalR406BelowCombined B cutoff terminal)
    }

  directCombinedGrowthAndPaymentBuildBarrier :
    (cutoff : Nat) →
    (terminal : Time) →
    (G : DirectCombinedCriticalGrowthPayment cutoff terminal) →
    (P : Combined.CutoffUniformCombinedSelfExternalPayment) →
    let
      margin = retainedMargin G
    in
    Obs.criticalEnergyAt T cutoff terminal
      + margin * Obs.integratedCriticalDissipation T cutoff terminal
    ≤
    Obs.criticalEnergyAt T cutoff initialTime
      + R700.twelve
          * Combined.cutoffIndependentBound P terminal
  directCombinedGrowthAndPaymentBuildBarrier cutoff terminal G P =
    let
      xT = Obs.criticalEnergyAt T cutoff terminal
      x0 = Obs.criticalEnergyAt T cutoff initialTime
      margin = retainedMargin G
      diss = Obs.integratedCriticalDissipation T cutoff terminal
      combined = Combined.integratedCombinedSelfExternal cutoff terminal
      bound = Combined.cutoffIndependentBound P terminal

      growthUpper :
        xT - x0 + margin * diss ≤ combined
      growthUpper = criticalGrowthPaidByCombined G

      combinedUpper :
        combined
        ≤
        R700.twelve
          * bound
      combinedUpper =
        Combined.combinedSelfExternalPayment P cutoff terminal

      composed :
        xT - x0 + margin * diss
        ≤
        R700.twelve
          * bound
      composed = ℚP.≤-trans growthUpper combinedUpper

      shifted :
        (xT - x0 + margin * diss) + x0
        ≤
        (R700.twelve
          * bound) + x0
      shifted = ℚP.+-mono-≤ composed ℚP.≤-refl
    in
    subst
      (λ rhs →
        xT + margin * diss ≤ rhs)
      (solve (x0 ∷ bound ∷ Fold.two ∷ []))
      (subst
        (λ lhs →
          lhs
          ≤
          (R700.twelve
            * bound) + x0)
        (solve (xT ∷ x0 ∷ margin ∷ diss ∷ []))
        shifted)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round730R726PlusC2BuildDirectCombinedGrowth : Bool
round730R726PlusC2BuildDirectCombinedGrowth = true

round730DirectCombinedGrowthBypassesLiteralR406AtTerminalCut : Bool
round730DirectCombinedGrowthBypassesLiteralR406AtTerminalCut = true

round730DirectCombinedGrowthPlusR723BuildsCriticalBarrier : Bool
round730DirectCombinedGrowthPlusR723BuildsCriticalBarrier = true

round730SeparateR726TransportMandatoryAfterDirectRecut : Bool
round730SeparateR726TransportMandatoryAfterDirectRecut = false

round730SeparateStrictMarginC2MandatoryAfterDirectRecut : Bool
round730SeparateStrictMarginC2MandatoryAfterDirectRecut = false

round730DirectCombinedCriticalGrowthPaymentClosed : Bool
round730DirectCombinedCriticalGrowthPaymentClosed = false

round730R723CombinedPaymentClosed : Bool
round730R723CombinedPaymentClosed =
  R723.round723CombinedCutoffUniformPaymentClosed

round730IntroducesEstimate : Bool
round730IntroducesEstimate = false

round730ClayPromotion : Bool
round730ClayPromotion = false

round730R726PlusC2BuildDirectCombinedGrowthIsTrue :
  round730R726PlusC2BuildDirectCombinedGrowth ≡ true
round730R726PlusC2BuildDirectCombinedGrowthIsTrue = refl

round730DirectCombinedGrowthBypassesLiteralR406AtTerminalCutIsTrue :
  round730DirectCombinedGrowthBypassesLiteralR406AtTerminalCut ≡ true
round730DirectCombinedGrowthBypassesLiteralR406AtTerminalCutIsTrue = refl

round730DirectCombinedGrowthPlusR723BuildsCriticalBarrierIsTrue :
  round730DirectCombinedGrowthPlusR723BuildsCriticalBarrier ≡ true
round730DirectCombinedGrowthPlusR723BuildsCriticalBarrierIsTrue = refl

round730SeparateR726TransportMandatoryAfterDirectRecutIsFalse :
  round730SeparateR726TransportMandatoryAfterDirectRecut ≡ false
round730SeparateR726TransportMandatoryAfterDirectRecutIsFalse = refl

round730SeparateStrictMarginC2MandatoryAfterDirectRecutIsFalse :
  round730SeparateStrictMarginC2MandatoryAfterDirectRecut ≡ false
round730SeparateStrictMarginC2MandatoryAfterDirectRecutIsFalse = refl

round730DirectCombinedCriticalGrowthPaymentClosedIsFalse :
  round730DirectCombinedCriticalGrowthPaymentClosed ≡ false
round730DirectCombinedCriticalGrowthPaymentClosedIsFalse = refl

round730R723CombinedPaymentClosedIsFalse :
  round730R723CombinedPaymentClosed ≡ false
round730R723CombinedPaymentClosedIsFalse =
  R723.round723CombinedCutoffUniformPaymentClosedIsFalse

round730IntroducesEstimateIsFalse :
  round730IntroducesEstimate ≡ false
round730IntroducesEstimateIsFalse = refl

round730ClayPromotionIsFalse :
  round730ClayPromotion ≡ false
round730ClayPromotionIsFalse = refl
