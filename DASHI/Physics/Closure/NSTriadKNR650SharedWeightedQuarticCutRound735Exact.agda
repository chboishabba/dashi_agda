{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SharedWeightedQuarticCutRound735Exact where

------------------------------------------------------------------------
-- ROUND735 / PREFERRED TWO-LEAF CUT ON ONE QUARTIC WEIGHTED CARRIER
--
-- R731 produces the old A/R723 combined payment from
--
--   A' : W_N(T) + E_M,N(T) <= B(T),
--
-- while R734 rewrites the direct D leaf exactly as
--
--   D' :
--     [X_N(T) - 12 E_M,N(T)]
--       - [X_N(0) - 12 E_M,N(0)]
--       + delta D_N(T)
--     <= 12 W_N(T).
--
-- Thus both remaining analytic leaves may be searched on the SAME signed
-- weighted/input-Laplacian carrier W_N and the same coherent mixed endpoint.
--
-- Combining A' and D':
--
--   X_N(T) + delta D_N(T)
--     <= X_N(0) + 12 B(T) - 12 E_M,N(0)
--     <= X_N(0) + 12 B(T),
--
-- using only E_M,N(0) >= 0.
--
-- This removes the quintic R691 commutator from the preferred analytic target
-- entirely.  It does not prove A' or D'.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_; nonNegative)
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
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700
import DASHI.Physics.Closure.NSTriadKNR650GlobalMixedEnergyEndpointUpperRound699Exact as R699
import DASHI.Physics.Closure.NSTriadKNR650WeightedEndpointToCombinedPaymentRound731Exact as R731
import DASHI.Physics.Closure.NSTriadKNR650AugmentedCriticalWeightedNormalFormRound734Exact as R734
import DASHI.Physics.Closure.NSTriadKNR650TerminalMixedMassQPlusMinusRound733Exact as R733
import DASHI.Physics.Closure.NSTriadKNR650RateKernelInputLaplacianCollapseRound684Exact as R684

F : C3.RealField _
F = Rational.rationalRealField

module SharedWeightedCut
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

  module Aug = R734.AugmentedWeighted
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

  module Producer = R731.WeightedEndpointProducer
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus
    FTC integrationLinearity integrationTransport D

  module Balance = Upper.Balance
  module Obs = Aug.Obs
  module Direct = Aug.Direct

  T = Aug.T

  record CutoffUniformWeightedPlusTerminalPayment : Set₁ where
    field
      cutoffIndependentBound : Time → ℚ
      weightedPlusTerminalPayment :
        (cutoff : Nat) (terminal : Time) →
        Balance.globalIntegratedWeighted cutoff terminal
          + Upper.globalSelfEnergy cutoff terminal
        ≤ cutoffIndependentBound terminal

  open CutoffUniformWeightedPlusTerminalPayment public

  record SharedWeightedQuarticInputs
      (cutoff : Nat)
      (terminal : Time) : Set₁ where
    field
      weightedPlusTerminal :
        CutoffUniformWeightedPlusTerminalPayment

      augmentedCritical :
        Aug.AugmentedCriticalWeightedPayment cutoff terminal

  open SharedWeightedQuarticInputs public

  weightedPlusTerminalBuildsCombinedPayment :
    CutoffUniformWeightedPlusTerminalPayment →
    Aug.Combined.CutoffUniformCombinedSelfExternalPayment
  weightedPlusTerminalBuildsCombinedPayment P = record
    { Aug.Combined.cutoffIndependentBound =
        cutoffIndependentBound P
    ; Aug.Combined.combinedSelfExternalPayment =
        λ cutoff terminal →
          let
            commUpper :
              Balance.globalIntegratedCommutator cutoff terminal
              ≤ cutoffIndependentBound P terminal
            commUpper =
              ℚP.≤-trans
                (Producer.globalCommutatorBelowWeightedPlusTerminal
                  cutoff terminal)
                (weightedPlusTerminalPayment P cutoff terminal)

            scaled :
              R700.twelve * Balance.globalIntegratedCommutator cutoff terminal
              ≤ R700.twelve * cutoffIndependentBound P terminal
            scaled =
              let instance twelveNNI = nonNegative R731.twelveNN
              in ℚP.*-monoˡ-≤-nonNeg R700.twelve commUpper
          in
          subst
            (λ left →
              left ≤ R700.twelve * cutoffIndependentBound P terminal)
            (sym
              (Aug.Combined.integratedCombinedIsTwelveR691Commutator
                cutoff terminal))
            scaled
    }

  sharedWeightedInputsBuildBarrier :
    (cutoff : Nat) (terminal : Time) →
    SharedWeightedQuarticInputs cutoff terminal →
    let
      margin = Aug.retainedMargin (augmentedCritical _)
    in
    Obs.criticalEnergyAt T cutoff terminal
      + margin * Obs.integratedCriticalDissipation T cutoff terminal
    ≤
    Obs.criticalEnergyAt T cutoff initialTime
      + R700.twelve
          * cutoffIndependentBound (weightedPlusTerminal _) terminal
  sharedWeightedInputsBuildBarrier cutoff terminal I =
    Direct.directCombinedGrowthAndPaymentBuildBarrier
      cutoff
      terminal
      (Aug.augmentedBuildsDirect
        cutoff terminal (augmentedCritical I))
      (weightedPlusTerminalBuildsCombinedPayment
        (weightedPlusTerminal I))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round735PreferredCutUsesOneSharedWeightedCarrier : Bool
round735PreferredCutUsesOneSharedWeightedCarrier = true

round735QuinticCommutatorAbsentFromBothPreferredLeaves : Bool
round735QuinticCommutatorAbsentFromBothPreferredLeaves = true

round735WeightedCarrierHasInputLaplacianNormalForm : Bool
round735WeightedCarrierHasInputLaplacianNormalForm =
  R684.round684PhysicalRateKernelIsInputLaplacianWork

round735TerminalEndpointIsCanonicalQPlusMinus : Bool
round735TerminalEndpointIsCanonicalQPlusMinus =
  R733.round733R691EndpointIsCanonicalR227QPlusMinus

round735WeightedPlusTerminalPaymentClosed : Bool
round735WeightedPlusTerminalPaymentClosed = false

round735AugmentedCriticalWeightedPaymentClosed : Bool
round735AugmentedCriticalWeightedPaymentClosed =
  R734.round734AugmentedWeightedPaymentClosed

round735TwoSharedWeightedLeavesBuildBarrier : Bool
round735TwoSharedWeightedLeavesBuildBarrier = true

round735IntroducesEstimate : Bool
round735IntroducesEstimate = false

round735ClayPromotion : Bool
round735ClayPromotion = false

round735PreferredCutUsesOneSharedWeightedCarrierIsTrue :
  round735PreferredCutUsesOneSharedWeightedCarrier ≡ true
round735PreferredCutUsesOneSharedWeightedCarrierIsTrue = refl

round735QuinticCommutatorAbsentFromBothPreferredLeavesIsTrue :
  round735QuinticCommutatorAbsentFromBothPreferredLeaves ≡ true
round735QuinticCommutatorAbsentFromBothPreferredLeavesIsTrue = refl

round735WeightedCarrierHasInputLaplacianNormalFormIsTrue :
  round735WeightedCarrierHasInputLaplacianNormalForm ≡ true
round735WeightedCarrierHasInputLaplacianNormalFormIsTrue =
  R684.round684PhysicalRateKernelIsInputLaplacianWorkIsTrue

round735TerminalEndpointIsCanonicalQPlusMinusIsTrue :
  round735TerminalEndpointIsCanonicalQPlusMinus ≡ true
round735TerminalEndpointIsCanonicalQPlusMinusIsTrue =
  R733.round733R691EndpointIsCanonicalR227QPlusMinusIsTrue

round735WeightedPlusTerminalPaymentClosedIsFalse :
  round735WeightedPlusTerminalPaymentClosed ≡ false
round735WeightedPlusTerminalPaymentClosedIsFalse = refl

round735AugmentedCriticalWeightedPaymentClosedIsFalse :
  round735AugmentedCriticalWeightedPaymentClosed ≡ false
round735AugmentedCriticalWeightedPaymentClosedIsFalse =
  R734.round734AugmentedWeightedPaymentClosedIsFalse

round735TwoSharedWeightedLeavesBuildBarrierIsTrue :
  round735TwoSharedWeightedLeavesBuildBarrier ≡ true
round735TwoSharedWeightedLeavesBuildBarrierIsTrue = refl

round735IntroducesEstimateIsFalse :
  round735IntroducesEstimate ≡ false
round735IntroducesEstimateIsFalse = refl

round735ClayPromotionIsFalse :
  round735ClayPromotion ≡ false
round735ClayPromotionIsFalse = refl
