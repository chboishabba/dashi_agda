{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650AugmentedDerivativeCollectedRound739Exact where

------------------------------------------------------------------------
-- ROUND739 / COLLECT THE LITERAL AUGMENTED DERIVATIVE BEFORE ESTIMATION
--
-- R737:
--
--   A_dot = X_dot - 12 Q_dot.
--
-- S1a/S1b:
--
--   X_dot = P - 2 nu d.
--
-- R738:
--
--   Q_dot = C - W.
--
-- Therefore exactly
--
--   A_dot = P - 2 nu d - 12 C + 12 W.
--
-- The R684 input-Laplacian carrier is the final +12 W term.  No sign has yet
-- been taken and no norm/absolute-value estimate appears.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

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
import DASHI.Physics.Closure.NSTriadKNR650AugmentedDerivativeInputLaplacianRound738Exact as R738

F : C3.RealField _
F = Rational.rationalRealField

module CollectedDerivative
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

  module P = R738.PointwiseGlobal
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus constantScaleCalculus scalarDerivativeAlgebra
    FTC integrationLinearity integrationTransport D C R

  module Der = P.Der
  module Aug = Der.Aug
  module Live = Der.Live

  productionAt : Nat → Time → ℚ
  productionAt cutoff time =
    Aug.Obs.productionRateAt Aug.T cutoff time

  dissipationAt : Nat → Time → ℚ
  dissipationAt cutoff time =
    Aug.Obs.dissipationRateAt Aug.T cutoff time

  twoNu : ℚ
  twoNu =
    Fold.two * Live.physicalViscosity (Live.support D)

  criticalTangentSplit :
    (cutoff : Nat) (time : Time) →
    Der.criticalEnergyTangent cutoff time
    ≡ productionAt cutoff time - twoNu * dissipationAt cutoff time
  criticalTangentSplit cutoff time =
    Der.Critical.liveCriticalEnergyTangentSplit D cutoff time

  augmentedTangentCollected :
    (cutoff : Nat) (time : Time) →
    Der.augmentedTangent cutoff time
    ≡
    productionAt cutoff time
      - twoNu * dissipationAt cutoff time
      - R700.twelve * P.globalCommutatorAt cutoff time
      + R700.twelve * P.globalWeightedAt cutoff time
  augmentedTangentCollected cutoff time =
    let
      xdot = Der.criticalEnergyTangent cutoff time
      qdot = Der.globalQPlusMinusTangent cutoff time
      prod = productionAt cutoff time
      diss = dissipationAt cutoff time
      comm = P.globalCommutatorAt cutoff time
      weighted = P.globalWeightedAt cutoff time

      expose :
        Der.augmentedTangent cutoff time
        ≡
        (prod - twoNu * diss)
          - R700.twelve * (comm - weighted)
      expose =
        trans
          (cong
            (λ value →
              value - R700.twelve * qdot)
            (criticalTangentSplit cutoff time))
          (cong
            (λ value →
              (prod - twoNu * diss) - R700.twelve * value)
            (P.qDotIsCommutatorMinusWeighted cutoff time))
    in
    trans expose
      (solve
        ( prod
        ∷ diss
        ∷ twoNu
        ∷ comm
        ∷ weighted
        ∷ R700.twelve
        ∷ []))

  augmentedTangentCollectedInputLaplacian :
    (cutoff : Nat) (time : Time) →
    Der.augmentedTangent cutoff time
    ≡
    productionAt cutoff time
      - twoNu * dissipationAt cutoff time
      - R700.twelve * P.globalCommutatorAt cutoff time
      + R700.twelve * P.globalInputLaplacianWorkAt cutoff time
  augmentedTangentCollectedInputLaplacian cutoff time =
    trans
      (augmentedTangentCollected cutoff time)
      (cong
        (λ weighted →
          productionAt cutoff time
            - twoNu * dissipationAt cutoff time
            - R700.twelve * P.globalCommutatorAt cutoff time
            + R700.twelve * weighted)
        (P.globalWeightedIsInputLaplacian cutoff time))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round739AugmentedDerivativeCollectedExactly : Bool
round739AugmentedDerivativeCollectedExactly = true

round739R684InputLaplacianSubstitutedExactly : Bool
round739R684InputLaplacianSubstitutedExactly = true

round739CollectedDerivativeContainsCommutator : Bool
round739CollectedDerivativeContainsCommutator = true

round739IntroducesEstimate : Bool
round739IntroducesEstimate = false

round739W2Closed : Bool
round739W2Closed = false

round739ClayPromotion : Bool
round739ClayPromotion = false

round739AugmentedDerivativeCollectedExactlyIsTrue :
  round739AugmentedDerivativeCollectedExactly ≡ true
round739AugmentedDerivativeCollectedExactlyIsTrue = refl

round739R684InputLaplacianSubstitutedExactlyIsTrue :
  round739R684InputLaplacianSubstitutedExactly ≡ true
round739R684InputLaplacianSubstitutedExactlyIsTrue = refl

round739CollectedDerivativeContainsCommutatorIsTrue :
  round739CollectedDerivativeContainsCommutator ≡ true
round739CollectedDerivativeContainsCommutatorIsTrue = refl

round739IntroducesEstimateIsFalse :
  round739IntroducesEstimate ≡ false
round739IntroducesEstimateIsFalse = refl

round739W2ClosedIsFalse :
  round739W2Closed ≡ false
round739W2ClosedIsFalse = refl

round739ClayPromotionIsFalse :
  round739ClayPromotion ≡ false
round739ClayPromotionIsFalse = refl
