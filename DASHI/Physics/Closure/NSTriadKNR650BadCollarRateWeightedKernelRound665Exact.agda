{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650BadCollarRateWeightedKernelRound665Exact where

------------------------------------------------------------------------
-- ROUND665 / LIVE BAD-COLLAR RESIDUAL -> RATE-WEIGHTED R225 KERNEL
--
-- R664 proves on the actual R661 full fibre
--
--   SelfRate + PairDiff = n * WeightedWork,
--
-- with
--
--   WeightedWork = sum_i r_i W(M,A_i).
--
-- The existing rate-weighted R225 collapse proves on the SAME complete fibre
--
--   W(M,K_r) = 4 * WeightedWork,
--
-- where K_r is the rate-weighted quadratic-kernel fold.
--
-- Therefore, exactly and without any estimate,
--
--   4 [SelfRate + PairDiff] = n W(M,K_r).
--
-- The literal trajectory already carries E/I/S/L/H and transverse velocity,
-- so the R225 physical helicity receipt is constructed directly at every
-- (N,t).  This puts the surviving bad-collar local scalar on the SAME
-- rate-weighted quadratic-kernel vocabulary used by the A3/Cauchy comparison.
--
-- No M2 majorization is required for this canonical signed route. R662/R663
-- remain valid fallback upper bounds.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputCollapseRound225Exact as R225
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNRateWeightedMixedHelicityKernelCollapseExact as RateKernel
import DASHI.Physics.Closure.NSTriadKNA3CenteredKernelNormalFormExact as A3Kernel

import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNR650BadCollarRateWeightedWorkRound664Exact as R664

F : C3.RealField _
F = Rational.rationalRealField

module LiveKernel
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

  module Weighted = R664.LiveWeightedWork
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC integrationLinearity D

  module End = Endpoint.Endpoint
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC D

  module Live = R408.LiteralDynamics
    Time initialTime integrateTo VectorDerivativeOf

  state = Live.stateTrajectory (Live.support D)

  L = Live.Base.L state
  H = Live.Base.H state

  physicalHelicityAt :
    (cutoff : Nat) (time : Time) →
    R225.PhysicalFixedOutputHelicityData
      End.E End.I End.S L H (End.velocityAt cutoff time)
  physicalHelicityAt cutoff time =
    R225.physical-fixed-output-helicity-data
      (Live.Base.velocityTransverse state cutoff time)

  rateWeightedKernelAt :
    Nat → Z3.FourierMode → Time → C3.Complex3 F
  rateWeightedKernelAt cutoff output time =
    R224.foldVector
      (RateKernel.weightedIQuadraticKernel
        (RateKernel.physicalRateWeight (End.rateAt cutoff time))
        End.S
        (End.velocityAt cutoff time))
      (Output.physicalOutputFiber cutoff output)

  rateWeightedKernelWorkAt :
    Nat → Z3.FourierMode → Time → ℚ
  rateWeightedKernelWorkAt cutoff output time =
    Work.coherentWork
      (Weighted.Sp.mixedAt cutoff output time)
      (rateWeightedKernelAt cutoff output time)

  kernelWorkIsFourWeightedWork :
    (cutoff : Nat) (output : Z3.FourierMode) (time : Time) →
    rateWeightedKernelWorkAt cutoff output time
    ≡ A3Kernel.four * Weighted.weightedWorkAt cutoff output time
  kernelWorkIsFourWeightedWork cutoff output time =
    RateKernel.rateWeightedKernelWorkIsFourWeightedWork
      (physicalHelicityAt cutoff time)
      (End.rateAt cutoff time)
      cutoff output

  liveResidualIsRateWeightedKernel :
    (cutoff : Nat) (output : Z3.FourierMode) (time : Time) →
    A3Kernel.four *
      ( Weighted.Sp.rateSelfWorkAt cutoff output time
      + Weighted.Sp.pairDifferenceWorkAt cutoff output time )
    ≡
    Weighted.Sp.fibreCardinality cutoff output
      * rateWeightedKernelWorkAt cutoff output time
  liveResidualIsRateWeightedKernel cutoff output time =
    let
      residual =
        Weighted.Sp.rateSelfWorkAt cutoff output time
        + Weighted.Sp.pairDifferenceWorkAt cutoff output time

      n = Weighted.Sp.fibreCardinality cutoff output
      weighted = Weighted.weightedWorkAt cutoff output time
      kernelWork = rateWeightedKernelWorkAt cutoff output time

      residualMeaning : residual ≡ n * weighted
      residualMeaning =
        Weighted.liveRateSelfPlusPairDifferenceIsWeightedWork
          cutoff output time

      kernelMeaning : kernelWork ≡ A3Kernel.four * weighted
      kernelMeaning =
        kernelWorkIsFourWeightedWork cutoff output time
    in
    trans
      (cong (A3Kernel.four *_) residualMeaning)
      (trans
        (solve (A3Kernel.four ∷ n ∷ weighted ∷ []))
        (cong (n *_) (sym kernelMeaning)))

  integratedFourResidual :
    Nat → Z3.FourierMode → Time → ℚ
  integratedFourResidual cutoff output terminal =
    integrateTo
      (λ time →
        A3Kernel.four *
          ( Weighted.Sp.rateSelfWorkAt cutoff output time
          + Weighted.Sp.pairDifferenceWorkAt cutoff output time ))
      terminal

  integratedCardinalityKernelWork :
    Nat → Z3.FourierMode → Time → ℚ
  integratedCardinalityKernelWork cutoff output terminal =
    integrateTo
      (λ time →
        Weighted.Sp.fibreCardinality cutoff output
          * rateWeightedKernelWorkAt cutoff output time)
      terminal

  liveSpacetimeResidualIsRateWeightedKernel :
    (cutoff : Nat) (output : Z3.FourierMode) (terminal : Time) →
    integratedFourResidual cutoff output terminal
    ≡ integratedCardinalityKernelWork cutoff output terminal
  liveSpacetimeResidualIsRateWeightedKernel cutoff output terminal =
    Energy.integrationCongruent integrationLinearity
      (liveResidualIsRateWeightedKernel cutoff output)
      terminal

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round665LivePhysicalHelicityReceiptConstructed : Bool
round665LivePhysicalHelicityReceiptConstructed = true

round665LiveResidualRateWeightedKernelIdentityClosed : Bool
round665LiveResidualRateWeightedKernelIdentityClosed = true

round665LiveSpacetimeRateWeightedKernelIdentityClosed : Bool
round665LiveSpacetimeRateWeightedKernelIdentityClosed = true

round665SameRateWeightedKernelVocabularyAsA3Cauchy : Bool
round665SameRateWeightedKernelVocabularyAsA3Cauchy = true

round665M2MajorantRequiredForCanonicalRoute : Bool
round665M2MajorantRequiredForCanonicalRoute = false

round665RateWeightedKernelQuantitativePaymentClosed : Bool
round665RateWeightedKernelQuantitativePaymentClosed = false

round665CutoffUniformOutputAggregationClosed : Bool
round665CutoffUniformOutputAggregationClosed = false

round665IntroducesNewClayLeaf : Bool
round665IntroducesNewClayLeaf = false

round665C2Closed : Bool
round665C2Closed = false

round665ClayPromotion : Bool
round665ClayPromotion = false

round665LivePhysicalHelicityReceiptConstructedIsTrue :
  round665LivePhysicalHelicityReceiptConstructed ≡ true
round665LivePhysicalHelicityReceiptConstructedIsTrue = refl

round665LiveResidualRateWeightedKernelIdentityClosedIsTrue :
  round665LiveResidualRateWeightedKernelIdentityClosed ≡ true
round665LiveResidualRateWeightedKernelIdentityClosedIsTrue = refl

round665LiveSpacetimeRateWeightedKernelIdentityClosedIsTrue :
  round665LiveSpacetimeRateWeightedKernelIdentityClosed ≡ true
round665LiveSpacetimeRateWeightedKernelIdentityClosedIsTrue = refl

round665SameRateWeightedKernelVocabularyAsA3CauchyIsTrue :
  round665SameRateWeightedKernelVocabularyAsA3Cauchy ≡ true
round665SameRateWeightedKernelVocabularyAsA3CauchyIsTrue = refl

round665M2MajorantRequiredForCanonicalRouteIsFalse :
  round665M2MajorantRequiredForCanonicalRoute ≡ false
round665M2MajorantRequiredForCanonicalRouteIsFalse = refl

round665RateWeightedKernelQuantitativePaymentClosedIsFalse :
  round665RateWeightedKernelQuantitativePaymentClosed ≡ false
round665RateWeightedKernelQuantitativePaymentClosedIsFalse = refl

round665CutoffUniformOutputAggregationClosedIsFalse :
  round665CutoffUniformOutputAggregationClosed ≡ false
round665CutoffUniformOutputAggregationClosedIsFalse = refl

round665IntroducesNewClayLeafIsFalse :
  round665IntroducesNewClayLeaf ≡ false
round665IntroducesNewClayLeafIsFalse = refl

round665C2ClosedIsFalse :
  round665C2Closed ≡ false
round665C2ClosedIsFalse = refl

round665ClayPromotionIsFalse :
  round665ClayPromotion ≡ false
round665ClayPromotionIsFalse = refl
