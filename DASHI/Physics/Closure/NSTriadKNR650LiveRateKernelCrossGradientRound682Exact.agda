{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650LiveRateKernelCrossGradientRound682Exact where

------------------------------------------------------------------------
-- ROUND682 / ATTACH R681 TO THE ACTUAL R664/R665 LITERAL TRAJECTORY
--
-- R681 is a fixed-physical-system theorem.  The literal R408 trajectory
-- already provides exactly such a physical system at every (N,t), with the
-- same velocity, embedding, inverse-square law and viscosity consumed by R664.
--
-- Therefore, on the actual live fibre,
--
--   WeightedWork(N,k,t)
--     =
--   nu(t) |k|^2 W(M,M)
--     - 2 nu(t) CrossGradientWork(N,k,t).
--
-- Combining with R664 gives
--
--   Q = n * WeightedWork
--
-- on the same object, so the remaining local analytic coordinate may be taken
-- to be the literal cross-gradient work rather than an arbitrary weighted
-- covariance.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _-_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputCrossGradientCovarianceExact as Cross
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as R30

import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNR650BadCollarRateWeightedWorkRound664Exact as R664
import DASHI.Physics.Closure.NSTriadKNR650RateKernelCrossGradientNormalFormRound681Exact as R681

F : C3.RealField _
F = Rational.rationalRealField

module LiveCrossGradient
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

  module W = R664.LiveWeightedWork
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC integrationLinearity D

  module End = Endpoint.Endpoint
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC D

  crossGradientWorkAt :
    Nat → Z3.FourierMode → Time → ℚ
  crossGradientWorkAt cutoff output time =
    let
      items = Output.physicalOutputFiber cutoff output
      value = D1a.mixedProductCell End.S (End.velocityAt cutoff time)
      mixed = R224.foldVector value items
      work = Pair.cellWork mixed value
    in
    Pair.weightedWorkSum (R681.crossMultiplier End.E) work items

  selfWorkAt :
    Nat → Z3.FourierMode → Time → ℚ
  selfWorkAt cutoff output time =
    Work.coherentWork
      (W.Sp.mixedAt cutoff output time)
      (W.Sp.mixedAt cutoff output time)

  liveWeightedWorkCrossGradientNormalForm :
    (cutoff : Nat) (output : Z3.FourierMode) (time : Time) →
    W.weightedWorkAt cutoff output time
    ≡
    R30.viscosity (End.physicalSystemAt cutoff time)
      * C3.normSquared End.I output
      * selfWorkAt cutoff output time
      -
      (Cross.two * R30.viscosity (End.physicalSystemAt cutoff time))
        * crossGradientWorkAt cutoff output time
  liveWeightedWorkCrossGradientNormalForm cutoff output time =
    R681.physicalSystemRateWeightedWorkCrossGradientNormalForm
      (End.physicalSystemAt cutoff time)
      End.S
      output

  liveResidualCrossGradientNormalForm :
    (cutoff : Nat) (output : Z3.FourierMode) (time : Time) →
    W.Sp.rateSelfWorkAt cutoff output time
      + W.Sp.pairDifferenceWorkAt cutoff output time
    ≡
    W.Sp.fibreCardinality cutoff output
      *
      ( R30.viscosity (End.physicalSystemAt cutoff time)
          * C3.normSquared End.I output
          * selfWorkAt cutoff output time
        -
        (Cross.two * R30.viscosity (End.physicalSystemAt cutoff time))
          * crossGradientWorkAt cutoff output time )
  liveResidualCrossGradientNormalForm cutoff output time =
    trans
      (W.liveRateSelfPlusPairDifferenceIsWeightedWork cutoff output time)
      (cong
        (W.Sp.fibreCardinality cutoff output *_)
        (liveWeightedWorkCrossGradientNormalForm cutoff output time))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round682LiveR665WeightedWorkCrossGradientNormalFormClosed : Bool
round682LiveR665WeightedWorkCrossGradientNormalFormClosed = true

round682LiveResidualCrossGradientNormalFormClosed : Bool
round682LiveResidualCrossGradientNormalFormClosed = true

round682RemainingCoordinateUsesLiteralPDotQ : Bool
round682RemainingCoordinateUsesLiteralPDotQ = true

round682CrossGradientQuantitativePaymentClosed : Bool
round682CrossGradientQuantitativePaymentClosed = false

round682CutoffUniformAggregationClosed : Bool
round682CutoffUniformAggregationClosed = false

round682IntroducesEstimate : Bool
round682IntroducesEstimate = false

round682IntroducesNewClayLeaf : Bool
round682IntroducesNewClayLeaf = false

round682C2Closed : Bool
round682C2Closed = false

round682ClayPromotion : Bool
round682ClayPromotion = false

round682LiveR665WeightedWorkCrossGradientNormalFormClosedIsTrue :
  round682LiveR665WeightedWorkCrossGradientNormalFormClosed ≡ true
round682LiveR665WeightedWorkCrossGradientNormalFormClosedIsTrue = refl

round682LiveResidualCrossGradientNormalFormClosedIsTrue :
  round682LiveResidualCrossGradientNormalFormClosed ≡ true
round682LiveResidualCrossGradientNormalFormClosedIsTrue = refl

round682RemainingCoordinateUsesLiteralPDotQIsTrue :
  round682RemainingCoordinateUsesLiteralPDotQ ≡ true
round682RemainingCoordinateUsesLiteralPDotQIsTrue = refl

round682CrossGradientQuantitativePaymentClosedIsFalse :
  round682CrossGradientQuantitativePaymentClosed ≡ false
round682CrossGradientQuantitativePaymentClosedIsFalse = refl

round682CutoffUniformAggregationClosedIsFalse :
  round682CutoffUniformAggregationClosed ≡ false
round682CutoffUniformAggregationClosedIsFalse = refl

round682IntroducesEstimateIsFalse :
  round682IntroducesEstimate ≡ false
round682IntroducesEstimateIsFalse = refl

round682IntroducesNewClayLeafIsFalse :
  round682IntroducesNewClayLeaf ≡ false
round682IntroducesNewClayLeafIsFalse = refl

round682C2ClosedIsFalse :
  round682C2Closed ≡ false
round682C2ClosedIsFalse = refl

round682ClayPromotionIsFalse :
  round682ClayPromotion ≡ false
round682ClayPromotionIsFalse = refl
