{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CombinedRouteReturnsToRateKernelRound679Exact where

------------------------------------------------------------------------
-- ROUND679 / THE R676-R678 SIGNED HELICITY/TANGENT ROUTE CLOSES EXACTLY
--            BACK ONTO THE R665 RATE-WEIGHTED KERNEL
--
-- R678 leaves one signed self-channel mismatch:
--
--   16 Q = 4 (R * SelfKernelWork - 4 * A3).
--
-- But the existing centered A3 normal form says on the SAME complete fibre
--
--   4 * A3
--     = n * (- WeightedKernelWork)
--       + R * SelfKernelWork.
--
-- Hence
--
--   R * SelfKernelWork - 4 * A3
--     = n * WeightedKernelWork,
--
-- and therefore
--
--   16 Q = 4 n * WeightedKernelWork.
--
-- This is exactly the R665 scalar, only reached through the longer
-- external-helicity/tangent decomposition.  Consequently:
--
--   * R676's combined signed channel preserves cancellation correctly;
--   * R677/R678 reveal a genuine exact collapse;
--   * but the route does NOT create a new independent C2 payment coordinate.
--
-- Any quantitative theorem proved through the combined external-helicity /
-- tangent route must, after exact reduction, pay the same rate-weighted kernel
-- already identified in R665 unless it uses additional structure before this
-- collapse.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; Positive; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as R30
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNA3CenteredKernelNormalFormExact as Kernel
import DASHI.Physics.Closure.NSTriadKNR650BadCollarSingleSelfMismatchRound678Exact as R678

F : C3.RealField _
F = Rational.rationalRealField

module LiveLoop
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
    (scalarScaleCalculus :
      R416.ScalarConstantDerivativeCalculus
        Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (D :
      R408.LiteralDynamics.LiteralRHSTrajectoryData
        Time initialTime integrateTo VectorDerivativeOf) where

  module C = R678.LiveSingleMismatch
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC integrationLinearity D

  module At
      (cutoff : Nat)
      (output : Z3.FourierMode)
      (time : Time)
      (viscosityPositive :
        Positive (R30.viscosity (C.C.C.N.End.physicalSystemAt cutoff time)))
      (outputNonzero : Z3.NonZeroMode output) where

    module Base = C.At
      cutoff output time viscosityPositive outputNonzero

    module M = Base.Base.Base.Base.Base.M

    rateTotal : ℚ
    rateTotal = M.rateTotal

    signedA3 : ℚ
    signedA3 = M.signedA3

    selfKernelWork : ℚ
    selfKernelWork = M.selfKernelWork

    weightedKernelWork : ℚ
    weightedKernelWork = M.weightedKernelWork

    fibreCardinality : ℚ
    fibreCardinality = M.n

    residual : ℚ
    residual = Base.residual

    selfKernelMismatchIsRateKernel :
      rateTotal * selfKernelWork - Kernel.four * signedA3
      ≡ fibreCardinality * weightedKernelWork
    selfKernelMismatchIsRateKernel =
      let
        centered = M.a3CenteredKernelNormalForm
      in
      trans
        (cong
          (λ a3 →
            rateTotal * selfKernelWork - a3)
          centered)
        (solve
          ( rateTotal
          ∷ selfKernelWork
          ∷ fibreCardinality
          ∷ weightedKernelWork
          ∷ Kernel.four
          ∷ []))

    sixteenResidualReturnsToRateKernel :
      (Kernel.four * Kernel.four) * residual
      ≡
      Kernel.four * (fibreCardinality * weightedKernelWork)
    sixteenResidualReturnsToRateKernel =
      trans
        Base.sixteenResidualIsSingleSelfKernelMismatch
        (cong
          (Kernel.four *_)
          selfKernelMismatchIsRateKernel)

------------------------------------------------------------------------
-- Status / route no-go.
------------------------------------------------------------------------

round679SelfKernelMismatchIsExactlyRateWeightedKernel : Bool
round679SelfKernelMismatchIsExactlyRateWeightedKernel = true

round679CombinedHelicityTangentRouteReturnsToR665Kernel : Bool
round679CombinedHelicityTangentRouteReturnsToR665Kernel = true

round679CombinedRouteCreatesIndependentC2PaymentCoordinate : Bool
round679CombinedRouteCreatesIndependentC2PaymentCoordinate = false

round679ExternalHelicitySeparatePaymentMandatory : Bool
round679ExternalHelicitySeparatePaymentMandatory = false

round679FluxTangentSeparatePaymentMandatory : Bool
round679FluxTangentSeparatePaymentMandatory = false

round679RateWeightedKernelQuantitativePaymentClosed : Bool
round679RateWeightedKernelQuantitativePaymentClosed = false

round679IntroducesEstimate : Bool
round679IntroducesEstimate = false

round679IntroducesNewClayLeaf : Bool
round679IntroducesNewClayLeaf = false

round679C2Closed : Bool
round679C2Closed = false

round679ClayPromotion : Bool
round679ClayPromotion = false

round679SelfKernelMismatchIsExactlyRateWeightedKernelIsTrue :
  round679SelfKernelMismatchIsExactlyRateWeightedKernel ≡ true
round679SelfKernelMismatchIsExactlyRateWeightedKernelIsTrue = refl

round679CombinedHelicityTangentRouteReturnsToR665KernelIsTrue :
  round679CombinedHelicityTangentRouteReturnsToR665Kernel ≡ true
round679CombinedHelicityTangentRouteReturnsToR665KernelIsTrue = refl

round679CombinedRouteCreatesIndependentC2PaymentCoordinateIsFalse :
  round679CombinedRouteCreatesIndependentC2PaymentCoordinate ≡ false
round679CombinedRouteCreatesIndependentC2PaymentCoordinateIsFalse = refl

round679ExternalHelicitySeparatePaymentMandatoryIsFalse :
  round679ExternalHelicitySeparatePaymentMandatory ≡ false
round679ExternalHelicitySeparatePaymentMandatoryIsFalse = refl

round679FluxTangentSeparatePaymentMandatoryIsFalse :
  round679FluxTangentSeparatePaymentMandatory ≡ false
round679FluxTangentSeparatePaymentMandatoryIsFalse = refl

round679RateWeightedKernelQuantitativePaymentClosedIsFalse :
  round679RateWeightedKernelQuantitativePaymentClosed ≡ false
round679RateWeightedKernelQuantitativePaymentClosedIsFalse = refl

round679IntroducesEstimateIsFalse :
  round679IntroducesEstimate ≡ false
round679IntroducesEstimateIsFalse = refl

round679IntroducesNewClayLeafIsFalse :
  round679IntroducesNewClayLeaf ≡ false
round679IntroducesNewClayLeafIsFalse = refl

round679C2ClosedIsFalse :
  round679C2Closed ≡ false
round679C2ClosedIsFalse = refl

round679ClayPromotionIsFalse :
  round679ClayPromotion ≡ false
round679ClayPromotionIsFalse = refl
