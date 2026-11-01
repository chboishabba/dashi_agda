{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650BadCollarSpacetimePairDifferenceRound661Exact where

------------------------------------------------------------------------
-- ROUND661 / ACTIVE BAD-COLLAR SPACETIME PAIR-DIFFERENCE NORMAL FORM
--
-- R660 gives pointwise, on the SAME physical output fibre,
--
--   n W_bad(M,C)
--     = n W(M,T)
--       + (sum_i r_i) W(M,M)
--       + PairDiffWork.
--
-- R427/d1b1 already prove that the damped tangent T is the actual derivative
-- tangent of the coherent mixed-product sum.  Therefore, using only the
-- standard scalar FTC/integration-linearity authority already isolated by C6,
--
--   n integral W_bad(M,C)
--     = n [ E_M(T) - E_M(0) ]
--       + integral (sum_i r_i) W(M,M)
--       + integral PairDiffWork.
--
-- Here E_M = Re<M,M> and n is the fixed fibre cardinality.
--
-- This is the literal active bad-collar spacetime scalar.  The remaining
-- analytic problem is not endpoint calculus: it is a quantitative payment of
-- the signed self-rate + pair-difference contribution (or an equivalent direct
-- estimate), followed by the already-known output aggregation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralRHSPhysicalTrajectoryRound408Exact as R408
import DASHI.Physics.Closure.NSTriadKNActualMixedCellDerivativeRound426Exact as R426
import DASHI.Physics.Closure.NSTriadKNDoubleMixedActualDerivativeCompilerRound425Exact as R425
import DASHI.Physics.Closure.NSTriadKNR291ActualGramDerivativeCompilerRound417Exact as R417
import DASHI.Physics.Closure.NSTriadKNR290PairFluxDerivativeCompilerRound416Exact as R416
import DASHI.Physics.Closure.NSTriadKNSelfFluxScalarFTCBoundaryRound564Exact as R564
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalEnergyCalculusExact as Energy
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedEndpointCompilerExact as Endpoint
import DASHI.Physics.Closure.NSTriadKNFixedOutputMixedCommutatorDampedTangentExact as D1a
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNOutputLocalSelectorFixedOutputReductionExact as OutputLocal
import DASHI.Physics.Closure.NSTriadKNR650EuclideanCollarRefinementRound656Exact as R656
import DASHI.Physics.Closure.NSTriadKNR650BadCollarDivisionFreePairDifferenceRound660Exact as R660

F : C3.RealField _
F = Rational.rationalRealField

module Spacetime
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (VectorDerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (ScalarDerivativeOf : (Time → ℚ) → (Time → ℚ) → Set)
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
      R416.ScalarConstantDerivativeCalculus Time ScalarDerivativeOf)
    (FTC :
      R564.ScalarFundamentalTheorem564
        Time initialTime integrateTo ScalarDerivativeOf)
    (integrationLinearity :
      Energy.ScalarIntegrationLinearity Time integrateTo)
    (D : R408.LiteralDynamics.LiteralRHSTrajectoryData
      Time initialTime integrateTo VectorDerivativeOf) where

  module End = Endpoint.Endpoint
    Time initialTime integrateTo
    VectorDerivativeOf ScalarDerivativeOf
    projectedCross vectorAlgebra zeroCalculus
    hermitianCalculus scalarScaleCalculus FTC D

  S : Helical.HelicalModeScalars F
  S = End.S

  fibreCardinality :
    Nat → Z3.FourierMode → ℚ
  fibreCardinality cutoff output =
    Pair.natAsRational
      (length (Output.physicalOutputFiber cutoff output))

  mixedAt :
    Nat → Z3.FourierMode → Time → C3.Complex3 F
  mixedAt cutoff output time =
    Work.fixedOutputMixedProduct
      S (End.velocityAt cutoff time) cutoff output

  mixedAtIsEndpointCurve :
    (cutoff : Nat) (output : Z3.FourierMode) (time : Time) →
    mixedAt cutoff output time
    ≡ End.fixedOutputMixedCurve cutoff output time
  mixedAtIsEndpointCurve cutoff output time = refl

  dampedTangentWorkAt :
    Nat → Z3.FourierMode → Time → ℚ
  dampedTangentWorkAt cutoff output time =
    Work.coherentWork
      (mixedAt cutoff output time)
      (Work.fixedOutputDampedTangent
        (End.rateAt cutoff time)
        S
        (End.velocityAt cutoff time)
        (End.forcingAt cutoff time)
        cutoff output)

  dampedTangentWorkIsEndpointTangent :
    (cutoff : Nat) (output : Z3.FourierMode) (time : Time) →
    dampedTangentWorkAt cutoff output time
    ≡ End.coherentTangentWork cutoff output time
  dampedTangentWorkIsEndpointTangent cutoff output time =
    let
      mixed = End.fixedOutputMixedCurve cutoff output time
      actual = End.fixedOutputActualTangent cutoff output time
      damped = End.fixedOutputDampedTangent cutoff output time
      tangentEq : actual ≡ damped
      tangentEq =
        End.fixedOutputActualTangentIsDampedTangent
          cutoff output time
    in
    trans
      (cong
        (λ left →
          Work.coherentWork left
            (Work.fixedOutputDampedTangent
              (End.rateAt cutoff time)
              S
              (End.velocityAt cutoff time)
              (End.forcingAt cutoff time)
              cutoff output))
        (mixedAtIsEndpointCurve cutoff output time))
      (trans
        refl
        (cong (Work.coherentWork mixed) (sym tangentEq)))

  weightedBadCollarCommutatorWorkAt :
    Nat → Nat → Z3.FourierMode → Time → ℚ
  weightedBadCollarCommutatorWorkAt K cutoff output time =
    let
      items = Output.physicalOutputFiber cutoff output
      weightedCommutator =
        R224.foldVector
          (R294.weightedCommutatorCell
            (OutputLocal.outputLocalSwapInvariantWeight
              F (R656.badCollarPacket K))
            S
            (End.velocityAt cutoff time)
            (End.forcingAt cutoff time))
          items
    in
    Work.coherentWork (mixedAt cutoff output time) weightedCommutator

  rateSelfWorkAt :
    Nat → Z3.FourierMode → Time → ℚ
  rateSelfWorkAt cutoff output time =
    let
      items = Output.physicalOutputFiber cutoff output
      rate = Pair.cellRate (End.rateAt cutoff time)
      mixed = mixedAt cutoff output time
    in
    Pair.rateSum rate items * Work.coherentWork mixed mixed

  pairDifferenceWorkAt :
    Nat → Z3.FourierMode → Time → ℚ
  pairDifferenceWorkAt cutoff output time =
    let
      items = Output.physicalOutputFiber cutoff output
      value = D1a.mixedProductCell S (End.velocityAt cutoff time)
      mixed = mixedAt cutoff output time
      rate = Pair.cellRate (End.rateAt cutoff time)
      work = Pair.cellWork mixed value
    in
    Pair.pairDifferenceWorkSum rate work items

  pointwiseBadCollarDivisionFree :
    (K cutoff : Nat) →
    (output : Z3.FourierMode) →
    R656.badCollarPacket K output ≡ true →
    (time : Time) →
    let n = fibreCardinality cutoff output in
    n * weightedBadCollarCommutatorWorkAt K cutoff output time
    ≡
    n * dampedTangentWorkAt cutoff output time
      + rateSelfWorkAt cutoff output time
      + pairDifferenceWorkAt cutoff output time
  pointwiseBadCollarDivisionFree K cutoff output active time =
    R660.activeBadCollarWeightedCommutatorPairDifference
      K output active
      (End.rateAt cutoff time)
      S
      (End.velocityAt cutoff time)
      (End.forcingAt cutoff time)
      cutoff

  integratedDampedTangentEndpoint :
    (cutoff : Nat) →
    (output : Z3.FourierMode) →
    (terminal : Time) →
    let n = fibreCardinality cutoff output in
    integrateTo
      (λ time → n * dampedTangentWorkAt cutoff output time)
      terminal
    ≡
    n *
      (End.selfEnergy cutoff output terminal
        - End.selfEnergy cutoff output initialTime)
  integratedDampedTangentEndpoint cutoff output terminal =
    let
      n = fibreCardinality cutoff output

      congruent :
        integrateTo
          (dampedTangentWorkAt cutoff output)
          terminal
        ≡
        integrateTo
          (End.coherentTangentWork cutoff output)
          terminal
      congruent =
        Energy.integrationCongruent integrationLinearity
          (dampedTangentWorkIsEndpointTangent cutoff output)
          terminal

      scaled :
        integrateTo
          (λ time → n * dampedTangentWorkAt cutoff output time)
          terminal
        ≡
        n * integrateTo
          (dampedTangentWorkAt cutoff output)
          terminal
      scaled =
        Energy.integrationConstantScale integrationLinearity
          n (dampedTangentWorkAt cutoff output) terminal

      endpoint :
        integrateTo
          (End.coherentTangentWork cutoff output)
          terminal
        ≡
        End.selfEnergy cutoff output terminal
          - End.selfEnergy cutoff output initialTime
      endpoint =
        End.fixedOutputEndpointIdentity cutoff output terminal
    in
    trans
      scaled
      (trans
        (cong (n *_) congruent)
        (cong (n *_) endpoint))

  integratedBadCollarPairDifferenceNormalForm :
    (K cutoff : Nat) →
    (output : Z3.FourierMode) →
    R656.badCollarPacket K output ≡ true →
    (terminal : Time) →
    let n = fibreCardinality cutoff output in
    integrateTo
      (λ time →
        n * weightedBadCollarCommutatorWorkAt K cutoff output time)
      terminal
    ≡
    n *
      (End.selfEnergy cutoff output terminal
        - End.selfEnergy cutoff output initialTime)
      + integrateTo (rateSelfWorkAt cutoff output) terminal
      + integrateTo (pairDifferenceWorkAt cutoff output) terminal
  integratedBadCollarPairDifferenceNormalForm
      K cutoff output active terminal =
    let
      n = fibreCardinality cutoff output
      weighted =
        weightedBadCollarCommutatorWorkAt K cutoff output
      tangent = dampedTangentWorkAt cutoff output
      rateSelf = rateSelfWorkAt cutoff output
      pairDiff = pairDifferenceWorkAt cutoff output

      pointwise :
        (time : Time) →
        n * weighted time
        ≡ (n * tangent time + rateSelf time) + pairDiff time
      pointwise time =
        trans
          (pointwiseBadCollarDivisionFree
            K cutoff output active time)
          (solve
            ( n ∷ tangent time
            ∷ rateSelf time ∷ pairDiff time ∷ [] ))

      integratePointwise :
        integrateTo (λ time → n * weighted time) terminal
        ≡
        integrateTo
          (λ time → (n * tangent time + rateSelf time) + pairDiff time)
          terminal
      integratePointwise =
        Energy.integrationCongruent integrationLinearity
          pointwise terminal

      splitOuter :
        integrateTo
          (λ time → (n * tangent time + rateSelf time) + pairDiff time)
          terminal
        ≡
        integrateTo
          (λ time → n * tangent time + rateSelf time)
          terminal
          + integrateTo pairDiff terminal
      splitOuter =
        Energy.integrationAdditive integrationLinearity
          (λ time → n * tangent time + rateSelf time)
          pairDiff terminal

      splitInner :
        integrateTo
          (λ time → n * tangent time + rateSelf time)
          terminal
        ≡
        integrateTo (λ time → n * tangent time) terminal
          + integrateTo rateSelf terminal
      splitInner =
        Energy.integrationAdditive integrationLinearity
          (λ time → n * tangent time)
          rateSelf terminal

      endpoint =
        integratedDampedTangentEndpoint cutoff output terminal
    in
    trans
      integratePointwise
      (trans
        splitOuter
        (trans
          (cong
            (_+ integrateTo pairDiff terminal)
            splitInner)
          (trans
            (cong
              (λ value →
                value
                  + integrateTo rateSelf terminal
                  + integrateTo pairDiff terminal)
              endpoint)
            refl)))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round661ActiveBadCollarSpacetimePairDifferenceNormalFormClosed : Bool
round661ActiveBadCollarSpacetimePairDifferenceNormalFormClosed = true

round661EndpointTangentRemovedModuloStandardCalculus : Bool
round661EndpointTangentRemovedModuloStandardCalculus = true

round661SignedRateSelfPlusPairDifferencePaymentClosed : Bool
round661SignedRateSelfPlusPairDifferencePaymentClosed = false

round661CutoffUniformOutputAggregationClosed : Bool
round661CutoffUniformOutputAggregationClosed = false

round661IntroducesNewClayLeaf : Bool
round661IntroducesNewClayLeaf = false

round661C2Closed : Bool
round661C2Closed = false

round661ClayPromotion : Bool
round661ClayPromotion = false

round661ActiveBadCollarSpacetimePairDifferenceNormalFormClosedIsTrue :
  round661ActiveBadCollarSpacetimePairDifferenceNormalFormClosed ≡ true
round661ActiveBadCollarSpacetimePairDifferenceNormalFormClosedIsTrue = refl

round661EndpointTangentRemovedModuloStandardCalculusIsTrue :
  round661EndpointTangentRemovedModuloStandardCalculus ≡ true
round661EndpointTangentRemovedModuloStandardCalculusIsTrue = refl

round661SignedRateSelfPlusPairDifferencePaymentClosedIsFalse :
  round661SignedRateSelfPlusPairDifferencePaymentClosed ≡ false
round661SignedRateSelfPlusPairDifferencePaymentClosedIsFalse = refl

round661CutoffUniformOutputAggregationClosedIsFalse :
  round661CutoffUniformOutputAggregationClosed ≡ false
round661CutoffUniformOutputAggregationClosedIsFalse = refl

round661IntroducesNewClayLeafIsFalse :
  round661IntroducesNewClayLeaf ≡ false
round661IntroducesNewClayLeafIsFalse = refl

round661C2ClosedIsFalse :
  round661C2Closed ≡ false
round661C2ClosedIsFalse = refl

round661ClayPromotionIsFalse :
  round661ClayPromotion ≡ false
round661ClayPromotionIsFalse = refl
