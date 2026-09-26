{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650AugmentedCriticalWeightedNormalFormRound734Exact where

------------------------------------------------------------------------
-- ROUND734 / DIRECT LEAF D AS AUGMENTED CRITICAL ENERGY <= WEIGHTED WORK
--
-- R730's Pareto leaf is
--
--   X_N(T) - X_N(0) + delta D_N(T)
--     <= IntegratedCombined_N(T).
--
-- R723 and R691 give exactly
--
--   IntegratedCombined_N(T)
--     = 12 * C_N(T)
--     = 12 * [ W_N(T) + E_M,N(T) - E_M,N(0) ].
--
-- Hence R730 is equivalent to
--
--   [X_N(T) - 12 E_M,N(T)]
--     - [X_N(0) - 12 E_M,N(0)]
--     + delta D_N(T)
--   <= 12 W_N(T).
--
-- This is the preferred analytic normal form for D: the quintic commutator has
-- disappeared from the target.  R684 identifies the instantaneous weighted
-- scalar W with viscosity times one input-Laplacian coherent work, so theorem
-- search may stay on that signed quartic carrier.
--
-- No estimate is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

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
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700
import DASHI.Physics.Closure.NSTriadKNR650CombinedSelfExternalSpacetimeRound723Exact as R723
import DASHI.Physics.Closure.NSTriadKNR650GlobalMixedEnergyEndpointUpperRound699Exact as R699
import DASHI.Physics.Closure.NSTriadKNR650DirectCombinedCriticalGrowthRound730Exact as R730
import DASHI.Physics.Closure.NSTriadKNR650RateKernelInputLaplacianCollapseRound684Exact as R684

F : C3.RealField _
F = Rational.rationalRealField

module AugmentedWeighted
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

  module Direct = R730.DirectCombinedGrowth
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Upper = R699.EndpointUpper
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus
    FTC integrationLinearity integrationTransport D

  module Balance = Upper.Balance
  module Combined = Direct.Combined
  module Obs = Direct.Obs
  module Growth = Direct.Growth

  T = Direct.T

  augmentedCriticalEnergy :
    Nat → Time → ℚ
  augmentedCriticalEnergy cutoff time =
    Obs.criticalEnergyAt T cutoff time
      - R700.twelve * Upper.globalSelfEnergy cutoff time

  augmentedCriticalGrowthWithMargin :
    Nat → ℚ → Time → ℚ
  augmentedCriticalGrowthWithMargin cutoff margin terminal =
    augmentedCriticalEnergy cutoff terminal
      - augmentedCriticalEnergy cutoff initialTime
      + margin * Obs.integratedCriticalDissipation T cutoff terminal

  combinedAsTwelveWeightedPlusEndpoint :
    (cutoff : Nat) (terminal : Time) →
    Combined.integratedCombinedSelfExternal cutoff terminal
    ≡
    R700.twelve *
      ( Balance.globalIntegratedWeighted cutoff terminal
      + Upper.globalSelfEnergy cutoff terminal
      - Upper.globalSelfEnergy cutoff initialTime )
  combinedAsTwelveWeightedPlusEndpoint cutoff terminal =
    let
      weighted = Balance.globalIntegratedWeighted cutoff terminal
      comm = Balance.globalIntegratedCommutator cutoff terminal
      eT = Upper.globalSelfEnergy cutoff terminal
      e0 = Upper.globalSelfEnergy cutoff initialTime

      combinedToComm =
        Combined.integratedCombinedIsTwelveR691Commutator cutoff terminal

      balance =
        Balance.globalMixedEnergyBalance cutoff terminal

      endpoint =
        Upper.globalEndpointDeltaIsTerminalMinusInitial cutoff terminal

      commMeaning :
        comm ≡ weighted + (eT - e0)
      commMeaning =
        let
          first :
            weighted ≡ comm - (eT - e0)
          first =
            subst
              (λ delta → weighted ≡ comm - delta)
              endpoint
              balance
        in
        subst
          (λ rhs → comm ≡ rhs)
          (solve (weighted ∷ comm ∷ eT ∷ e0 ∷ []))
          refl
    in
    trans
      combinedToComm
      (trans
        (Relation.Binary.PropositionalEquality.cong
          (R700.twelve *_) commMeaning)
        (solve
          ( R700.twelve
          ∷ weighted
          ∷ eT
          ∷ e0
          ∷ [])))

  directGrowthMinusEndpointIsAugmentedGrowth :
    (cutoff : Nat) (margin : ℚ) (terminal : Time) →
    Growth.criticalEnergyGrowthWithMargin D cutoff margin terminal
      - R700.twelve *
          ( Upper.globalSelfEnergy cutoff terminal
          - Upper.globalSelfEnergy cutoff initialTime )
    ≡ augmentedCriticalGrowthWithMargin cutoff margin terminal
  directGrowthMinusEndpointIsAugmentedGrowth cutoff margin terminal =
    solve
      ( Obs.criticalEnergyAt T cutoff terminal
      ∷ Obs.criticalEnergyAt T cutoff initialTime
      ∷ Upper.globalSelfEnergy cutoff terminal
      ∷ Upper.globalSelfEnergy cutoff initialTime
      ∷ margin
      ∷ Obs.integratedCriticalDissipation T cutoff terminal
      ∷ R700.twelve
      ∷ [])

  record AugmentedCriticalWeightedPayment
      (cutoff : Nat)
      (terminal : Time) : Set where
    field
      retainedMargin : ℚ
      retainedMarginPositive : 0 < retainedMargin
      augmentedGrowthPaidByWeighted :
        augmentedCriticalGrowthWithMargin cutoff retainedMargin terminal
        ≤ R700.twelve * Balance.globalIntegratedWeighted cutoff terminal

  open AugmentedCriticalWeightedPayment public

  directBuildsAugmented :
    (cutoff : Nat) (terminal : Time) →
    Direct.DirectCombinedCriticalGrowthPayment cutoff terminal →
    AugmentedCriticalWeightedPayment cutoff terminal
  directBuildsAugmented cutoff terminal P = record
    { retainedMargin = Direct.retainedMargin P
    ; retainedMarginPositive = Direct.retainedMarginPositive P
    ; augmentedGrowthPaidByWeighted =
        let
          margin = Direct.retainedMargin P
          growth =
            Growth.criticalEnergyGrowthWithMargin
              D cutoff margin terminal
          weighted = Balance.globalIntegratedWeighted cutoff terminal
          eT = Upper.globalSelfEnergy cutoff terminal
          e0 = Upper.globalSelfEnergy cutoff initialTime

          direct :
            growth ≤ Combined.integratedCombinedSelfExternal cutoff terminal
          direct = Direct.criticalGrowthPaidByCombined P

          combinedMeaning =
            combinedAsTwelveWeightedPlusEndpoint cutoff terminal

          exposed :
            growth
            ≤ R700.twelve * (weighted + eT - e0)
          exposed =
            subst
              (growth ≤_)
              combinedMeaning
              direct

          shifted :
            growth - R700.twelve * (eT - e0)
            ≤
            R700.twelve * (weighted + eT - e0)
              - R700.twelve * (eT - e0)
          shifted =
            ℚP.+-mono-≤ exposed ℚP.≤-refl

          normalized :
            growth - R700.twelve * (eT - e0)
            ≤ R700.twelve * weighted
          normalized =
            subst
              (λ rhs →
                growth - R700.twelve * (eT - e0) ≤ rhs)
              (solve (R700.twelve ∷ weighted ∷ eT ∷ e0 ∷ []))
              shifted
        in
        subst
          (λ lhs → lhs ≤ R700.twelve * weighted)
          (sym
            (directGrowthMinusEndpointIsAugmentedGrowth
              cutoff margin terminal))
          normalized
    }

  augmentedBuildsDirect :
    (cutoff : Nat) (terminal : Time) →
    AugmentedCriticalWeightedPayment cutoff terminal →
    Direct.DirectCombinedCriticalGrowthPayment cutoff terminal
  augmentedBuildsDirect cutoff terminal P = record
    { Direct.retainedMargin = retainedMargin P
    ; Direct.retainedMarginPositive = retainedMarginPositive P
    ; Direct.criticalGrowthPaidByCombined =
        let
          margin = retainedMargin P
          growth =
            Growth.criticalEnergyGrowthWithMargin
              D cutoff margin terminal
          weighted = Balance.globalIntegratedWeighted cutoff terminal
          eT = Upper.globalSelfEnergy cutoff terminal
          e0 = Upper.globalSelfEnergy cutoff initialTime

          aug :
            augmentedCriticalGrowthWithMargin cutoff margin terminal
            ≤ R700.twelve * weighted
          aug = augmentedGrowthPaidByWeighted P

          unshifted :
            growth
            ≤ R700.twelve * (weighted + eT - e0)
          unshifted =
            let
              exposed :
                growth - R700.twelve * (eT - e0)
                ≤ R700.twelve * weighted
              exposed =
                subst
                  (λ lhs → lhs ≤ R700.twelve * weighted)
                  (directGrowthMinusEndpointIsAugmentedGrowth
                    cutoff margin terminal)
                  aug

              shifted =
                ℚP.+-mono-≤ exposed ℚP.≤-refl
            in
            subst
              (λ lhs →
                lhs ≤
                  R700.twelve * weighted
                    + R700.twelve * (eT - e0))
              (solve (growth ∷ R700.twelve ∷ eT ∷ e0 ∷ []))
              (subst
                (λ rhs →
                  (growth - R700.twelve * (eT - e0))
                    + R700.twelve * (eT - e0)
                  ≤ rhs)
                (solve (R700.twelve ∷ weighted ∷ eT ∷ e0 ∷ []))
                shifted)
        in
        subst
          (growth ≤_)
          (sym (combinedAsTwelveWeightedPlusEndpoint cutoff terminal))
          unshifted
    }

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round734DirectLeafEquivalentToAugmentedWeightedPayment : Bool
round734DirectLeafEquivalentToAugmentedWeightedPayment = true

round734QuinticCommutatorAbsentFromPreferredDTarget : Bool
round734QuinticCommutatorAbsentFromPreferredDTarget = true

round734WeightedCarrierHasInputLaplacianNormalForm : Bool
round734WeightedCarrierHasInputLaplacianNormalForm =
  R684.round684PhysicalRateKernelIsInputLaplacianWork

round734AugmentedWeightedPaymentClosed : Bool
round734AugmentedWeightedPaymentClosed = false

round734IntroducesEstimate : Bool
round734IntroducesEstimate = false

round734ClayPromotion : Bool
round734ClayPromotion = false

round734DirectLeafEquivalentToAugmentedWeightedPaymentIsTrue :
  round734DirectLeafEquivalentToAugmentedWeightedPayment ≡ true
round734DirectLeafEquivalentToAugmentedWeightedPaymentIsTrue = refl

round734QuinticCommutatorAbsentFromPreferredDTargetIsTrue :
  round734QuinticCommutatorAbsentFromPreferredDTarget ≡ true
round734QuinticCommutatorAbsentFromPreferredDTargetIsTrue = refl

round734WeightedCarrierHasInputLaplacianNormalFormIsTrue :
  round734WeightedCarrierHasInputLaplacianNormalForm ≡ true
round734WeightedCarrierHasInputLaplacianNormalFormIsTrue =
  R684.round684PhysicalRateKernelIsInputLaplacianWorkIsTrue

round734AugmentedWeightedPaymentClosedIsFalse :
  round734AugmentedWeightedPaymentClosed ≡ false
round734AugmentedWeightedPaymentClosedIsFalse = refl

round734IntroducesEstimateIsFalse :
  round734IntroducesEstimate ≡ false
round734IntroducesEstimateIsFalse = refl

round734ClayPromotionIsFalse :
  round734ClayPromotion ≡ false
round734ClayPromotionIsFalse = refl
