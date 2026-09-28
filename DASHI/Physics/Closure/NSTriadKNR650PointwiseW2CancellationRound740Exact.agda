{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650PointwiseW2CancellationRound740Exact where

------------------------------------------------------------------------
-- ROUND740 / POINTWISE W2 CANCELLATION TEST
--
-- R739 gives
--
--   A_dot = P - 2nu d - 12 C + 12 W.
--
-- Therefore, for any retained margin delta,
--
--   A_dot + delta d <= 12 W
--
-- is EXACTLY equivalent to
--
--   P <= (2nu-delta) d + 12 C.
--
-- The +12 W term cancels from both sides.  Consequently substituting R684's
-- input-Laplacian normal form does NOT by itself turn W2 into a pure quartic
-- coercivity estimate.  The pointwise derivative route returns to a signed
-- production-vs-global-commutator inequality.
--
-- This is a structural reduction/no-shortcut result, not a negative theorem
-- about possible analytic estimates on the remaining signed residual.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

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
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700
import DASHI.Physics.Closure.NSTriadKNR650AugmentedDerivativeCollectedRound739Exact as R739

F : C3.RealField _
F = Rational.rationalRealField

module PointwiseCancellation
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

  module K = R739.CollectedDerivative
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  pointwiseW2 :
    Nat → Time → ℚ → Set
  pointwiseW2 cutoff time margin =
    K.Der.augmentedTangent cutoff time
      + margin * K.dissipationAt cutoff time
    ≤
    R700.twelve * K.P.globalWeightedAt cutoff time

  strictProductionVsCommutator :
    Nat → Time → ℚ → Set
  strictProductionVsCommutator cutoff time margin =
    K.productionAt cutoff time
    ≤
    (K.twoNu - margin) * K.dissipationAt cutoff time
      + R700.twelve * K.P.globalCommutatorAt cutoff time

  pointwiseW2ImpliesStrictProductionVsCommutator :
    (cutoff : Nat) (time : Time) (margin : ℚ) →
    pointwiseW2 cutoff time margin →
    strictProductionVsCommutator cutoff time margin
  pointwiseW2ImpliesStrictProductionVsCommutator
      cutoff time margin h =
    let
      prod = K.productionAt cutoff time
      diss = K.dissipationAt cutoff time
      comm = K.P.globalCommutatorAt cutoff time
      weighted = K.P.globalWeightedAt cutoff time
      aug = K.Der.augmentedTangent cutoff time
      twelveW = R700.twelve * weighted
      shift = K.twoNu * diss + R700.twelve * comm - margin * diss

      exposed :
        prod - K.twoNu * diss
          - R700.twelve * comm
          + twelveW
          + margin * diss
        ≤ twelveW
      exposed =
        subst
          (λ lhs → lhs + margin * diss ≤ twelveW)
          (K.augmentedTangentCollected cutoff time)
          h

      shifted :
        (prod - K.twoNu * diss
          - R700.twelve * comm
          + twelveW
          + margin * diss) + shift
        ≤ twelveW + shift
      shifted =
        ℚP.+-mono-≤ exposed ℚP.≤-refl

      normalized :
        prod + twelveW
        ≤
        ((K.twoNu - margin) * diss
          + R700.twelve * comm) + twelveW
      normalized =
        subst
          (λ lhs →
            lhs
            ≤ ((K.twoNu - margin) * diss
                + R700.twelve * comm) + twelveW)
          (solve
            ( prod ∷ diss ∷ comm ∷ weighted ∷ margin
            ∷ K.twoNu ∷ R700.twelve ∷ []))
          (subst
            (λ rhs →
              (prod - K.twoNu * diss
                - R700.twelve * comm
                + twelveW
                + margin * diss) + shift
              ≤ rhs)
            (solve
              ( prod ∷ diss ∷ comm ∷ weighted ∷ margin
              ∷ K.twoNu ∷ R700.twelve ∷ []))
            shifted)
    in
    ℚP.+-cancelʳ-≤ twelveW normalized

  strictProductionVsCommutatorImpliesPointwiseW2 :
    (cutoff : Nat) (time : Time) (margin : ℚ) →
    strictProductionVsCommutator cutoff time margin →
    pointwiseW2 cutoff time margin
  strictProductionVsCommutatorImpliesPointwiseW2
      cutoff time margin h =
    let
      prod = K.productionAt cutoff time
      diss = K.dissipationAt cutoff time
      comm = K.P.globalCommutatorAt cutoff time
      weighted = K.P.globalWeightedAt cutoff time
      aug = K.Der.augmentedTangent cutoff time
      twelveW = R700.twelve * weighted

      withCommon :
        prod + twelveW
        ≤
        ((K.twoNu - margin) * diss
          + R700.twelve * comm) + twelveW
      withCommon = ℚP.+-mono-≤ h ℚP.≤-refl

      normalized :
        prod - K.twoNu * diss
          - R700.twelve * comm
          + twelveW
          + margin * diss
        ≤ twelveW
      normalized =
        subst
          (λ lhs → lhs ≤ twelveW)
          (solve
            ( prod ∷ diss ∷ comm ∷ weighted ∷ margin
            ∷ K.twoNu ∷ R700.twelve ∷ []))
          (subst
            (λ rhs → prod + twelveW ≤ rhs)
            (solve
              ( prod ∷ diss ∷ comm ∷ weighted ∷ margin
              ∷ K.twoNu ∷ R700.twelve ∷ []))
            withCommon)
    in
    subst
      (λ lhs → lhs + margin * diss ≤ twelveW)
      (sym (K.augmentedTangentCollected cutoff time))
      normalized

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round740PointwiseW2ExactlyReturnsToProductionCommutator : Bool
round740PointwiseW2ExactlyReturnsToProductionCommutator = true

round740InputLaplacianSurvivesAfterMovingW2RHS : Bool
round740InputLaplacianSurvivesAfterMovingW2RHS = false

round740DerivativeRouteMakesW2PureQuarticCoercivityAutomatically : Bool
round740DerivativeRouteMakesW2PureQuarticCoercivityAutomatically = false

round740AdditionalSignedProductionCommutatorStructureRequired : Bool
round740AdditionalSignedProductionCommutatorStructureRequired = true

round740W2Closed : Bool
round740W2Closed = false

round740IntroducesEstimate : Bool
round740IntroducesEstimate = false

round740ClayPromotion : Bool
round740ClayPromotion = false

round740PointwiseW2ExactlyReturnsToProductionCommutatorIsTrue :
  round740PointwiseW2ExactlyReturnsToProductionCommutator ≡ true
round740PointwiseW2ExactlyReturnsToProductionCommutatorIsTrue = refl

round740InputLaplacianSurvivesAfterMovingW2RHSIsFalse :
  round740InputLaplacianSurvivesAfterMovingW2RHS ≡ false
round740InputLaplacianSurvivesAfterMovingW2RHSIsFalse = refl

round740DerivativeRouteMakesW2PureQuarticCoercivityAutomaticallyIsFalse :
  round740DerivativeRouteMakesW2PureQuarticCoercivityAutomatically ≡ false
round740DerivativeRouteMakesW2PureQuarticCoercivityAutomaticallyIsFalse = refl

round740AdditionalSignedProductionCommutatorStructureRequiredIsTrue :
  round740AdditionalSignedProductionCommutatorStructureRequired ≡ true
round740AdditionalSignedProductionCommutatorStructureRequiredIsTrue = refl

round740W2ClosedIsFalse :
  round740W2Closed ≡ false
round740W2ClosedIsFalse = refl

round740IntroducesEstimateIsFalse :
  round740IntroducesEstimate ≡ false
round740IntroducesEstimateIsFalse = refl

round740ClayPromotionIsFalse :
  round740ClayPromotion ≡ false
round740ClayPromotionIsFalse = refl
