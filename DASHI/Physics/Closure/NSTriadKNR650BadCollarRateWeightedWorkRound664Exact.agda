{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650BadCollarRateWeightedWorkRound664Exact where

------------------------------------------------------------------------
-- ROUND664 / R661 RESIDUAL = ONE RATE-WEIGHTED FULL-FIBRE WORK
--
-- R661 isolates on one active bad-collar output fibre
--
--   SelfRate + PairDiff
--
-- where
--
--   SelfRate = (sum_i r_i) W(M,M)
--   PairDiff = sum_{i<j}(r_i-r_j)(w_i-w_j)
--   w_i      = W(M,A_i)
--   M        = sum_i A_i.
--
-- The complete-graph identity already proved in the covariance owner is
--
--   PairDiff
--     = n sum_i r_i w_i - (sum_i r_i)(sum_i w_i),
--
-- and sum_i w_i = W(M,M).  Hence EXACTLY
--
--   SelfRate + PairDiff = n sum_i r_i W(M,A_i).
--
-- Thus the apparent positive self-rate coordinate is not an independent
-- analytic burden.  It recombines with the signed pair difference into ONE
-- rate-weighted coherent-work scalar.
--
-- On the literal R661 trajectory this equality lifts to spacetime using only
-- the already-isolated integration congruence authority.
--
-- R662/R663 remain valid absolute-M2 fallback majorants, but the canonical
-- signed search target after R664 is the rate-weighted full-fibre work itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair

import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNR650BadCollarSpacetimePairDifferenceRound661Exact as R661

F : C3.RealField _
F = Rational.rationalRealField

------------------------------------------------------------------------
-- Generic full-fibre identity.
------------------------------------------------------------------------

fixedOutputRateSelfPlusPairDifferenceIsWeightedWork :
  (rho : Z3.FourierMode → ℚ) →
  (S : Helical.HelicalModeScalars F) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) (output : Z3.FourierMode) →
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    rate = Pair.cellRate rho
    work = Pair.cellWork mixed value
    n = Pair.natAsRational (length items)
    selfRate =
      Pair.rateSum rate items * Work.coherentWork mixed mixed
    pairDiff =
      Pair.pairDifferenceWorkSum rate work items
    weighted =
      Pair.weightedWorkSum rate work items
  in
  selfRate + pairDiff ≡ n * weighted
fixedOutputRateSelfPlusPairDifferenceIsWeightedWork
    rho S velocity cutoff output =
  let
    items = Output.physicalOutputFiber cutoff output
    value = D1a.mixedProductCell S velocity
    mixed = R224.foldVector value items
    rate = Pair.cellRate rho
    work = Pair.cellWork mixed value
    n = Pair.natAsRational (length items)
    rateTotal = Pair.rateSum rate items
    self = Work.coherentWork mixed mixed
    weighted = Pair.weightedWorkSum rate work items
    pairDiff = Pair.pairDifferenceWorkSum rate work items

    pairClosed :
      pairDiff
      ≡ n * weighted - rateTotal * Pair.workSum work items
    pairClosed =
      Pair.pairDifferenceClosedForm rate work items

    workClosed :
      Pair.workSum work items ≡ self
    workClosed =
      Pair.workSumAgainstFold mixed value items
  in
  rewrite pairClosed | workClosed =
    solve (n ∷ weighted ∷ rateTotal ∷ self ∷ [])

------------------------------------------------------------------------
-- Same identity on the actual R661 trajectory.
------------------------------------------------------------------------

module LiveWeightedWork
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

  module Sp = R661.Spacetime
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC integrationLinearity D

  module End = Endpoint.Endpoint
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC D

  weightedWorkAt :
    Nat → Z3.FourierMode → Time → ℚ
  weightedWorkAt cutoff output time =
    let
      items = Output.physicalOutputFiber cutoff output
      rate = Pair.cellRate (End.rateAt cutoff time)
      work = End.workAt cutoff output time
    in
    Pair.weightedWorkSum rate work items

  cardinalityWeightedWorkAt :
    Nat → Z3.FourierMode → Time → ℚ
  cardinalityWeightedWorkAt cutoff output time =
    Sp.fibreCardinality cutoff output * weightedWorkAt cutoff output time

  liveRateSelfPlusPairDifferenceIsWeightedWork :
    (cutoff : Nat) (output : Z3.FourierMode) (time : Time) →
    Sp.rateSelfWorkAt cutoff output time
      + Sp.pairDifferenceWorkAt cutoff output time
    ≡ cardinalityWeightedWorkAt cutoff output time
  liveRateSelfPlusPairDifferenceIsWeightedWork cutoff output time =
    fixedOutputRateSelfPlusPairDifferenceIsWeightedWork
      (End.rateAt cutoff time)
      End.S
      (End.velocityAt cutoff time)
      cutoff output

  integratedRateSelfPlusPairDifference :
    Nat → Z3.FourierMode → Time → ℚ
  integratedRateSelfPlusPairDifference cutoff output terminal =
    integrateTo
      (λ time →
        Sp.rateSelfWorkAt cutoff output time
          + Sp.pairDifferenceWorkAt cutoff output time)
      terminal

  integratedCardinalityWeightedWork :
    Nat → Z3.FourierMode → Time → ℚ
  integratedCardinalityWeightedWork cutoff output terminal =
    integrateTo (cardinalityWeightedWorkAt cutoff output) terminal

  liveSpacetimeResidualIsCardinalityWeightedWork :
    (cutoff : Nat) (output : Z3.FourierMode) (terminal : Time) →
    integratedRateSelfPlusPairDifference cutoff output terminal
    ≡ integratedCardinalityWeightedWork cutoff output terminal
  liveSpacetimeResidualIsCardinalityWeightedWork
      cutoff output terminal =
    Energy.integrationCongruent integrationLinearity
      (liveRateSelfPlusPairDifferenceIsWeightedWork cutoff output)
      terminal

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round664FullFibreResidualWeightedWorkIdentityClosed : Bool
round664FullFibreResidualWeightedWorkIdentityClosed = true

round664LiveR661ResidualWeightedWorkIdentityClosed : Bool
round664LiveR661ResidualWeightedWorkIdentityClosed = true

round664LiveSpacetimeResidualWeightedWorkIdentityClosed : Bool
round664LiveSpacetimeResidualWeightedWorkIdentityClosed = true

round664SelfRateIsIndependentAnalyticLeaf : Bool
round664SelfRateIsIndependentAnalyticLeaf = false

round664M2MajorantRequiredForCanonicalRoute : Bool
round664M2MajorantRequiredForCanonicalRoute = false

round664RateWeightedWorkQuantitativePaymentClosed : Bool
round664RateWeightedWorkQuantitativePaymentClosed = false

round664CutoffUniformOutputAggregationClosed : Bool
round664CutoffUniformOutputAggregationClosed = false

round664IntroducesNewClayLeaf : Bool
round664IntroducesNewClayLeaf = false

round664C2Closed : Bool
round664C2Closed = false

round664ClayPromotion : Bool
round664ClayPromotion = false

round664FullFibreResidualWeightedWorkIdentityClosedIsTrue :
  round664FullFibreResidualWeightedWorkIdentityClosed ≡ true
round664FullFibreResidualWeightedWorkIdentityClosedIsTrue = refl

round664LiveR661ResidualWeightedWorkIdentityClosedIsTrue :
  round664LiveR661ResidualWeightedWorkIdentityClosed ≡ true
round664LiveR661ResidualWeightedWorkIdentityClosedIsTrue = refl

round664LiveSpacetimeResidualWeightedWorkIdentityClosedIsTrue :
  round664LiveSpacetimeResidualWeightedWorkIdentityClosed ≡ true
round664LiveSpacetimeResidualWeightedWorkIdentityClosedIsTrue = refl

round664SelfRateIsIndependentAnalyticLeafIsFalse :
  round664SelfRateIsIndependentAnalyticLeaf ≡ false
round664SelfRateIsIndependentAnalyticLeafIsFalse = refl

round664M2MajorantRequiredForCanonicalRouteIsFalse :
  round664M2MajorantRequiredForCanonicalRoute ≡ false
round664M2MajorantRequiredForCanonicalRouteIsFalse = refl

round664RateWeightedWorkQuantitativePaymentClosedIsFalse :
  round664RateWeightedWorkQuantitativePaymentClosed ≡ false
round664RateWeightedWorkQuantitativePaymentClosedIsFalse = refl

round664CutoffUniformOutputAggregationClosedIsFalse :
  round664CutoffUniformOutputAggregationClosed ≡ false
round664CutoffUniformOutputAggregationClosedIsFalse = refl

round664IntroducesNewClayLeafIsFalse :
  round664IntroducesNewClayLeaf ≡ false
round664IntroducesNewClayLeafIsFalse = refl

round664C2ClosedIsFalse :
  round664C2Closed ≡ false
round664C2ClosedIsFalse = refl

round664ClayPromotionIsFalse :
  round664ClayPromotion ≡ false
round664ClayPromotionIsFalse = refl
