module DASHI.Mathematics.NumberTheory.PartitionErdosBishopKMajorCoordinateDominationExact where

------------------------------------------------------------------------
-- POINTWISE ANALYTIC DOMINATION ON THE CERTIFIED K-MAJOR CARRIER
--
-- A coordinate (k,v) with k*v<=n decodes to the existing PositiveFactorPair.
-- The already-proved factor-pair exponential theorem then gives
--
--   v* exp(c sqrt(n-kv))
--     <= v* q(k*x_n)^v * exp(c sqrt n).
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopCubicTranslationIteratedExact as Iterated
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopNatRealPositiveExact as NatPositive
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact as Rate
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorPairCubicExponentialExact as FactorExp
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorPairCubicResidualExact as FactorResidual
import DASHI.Mathematics.NumberTheory.PartitionErdosKMajorFactorCoordinateExact as KMajor
open import DASHI.Physics.YangMills.CompactLieProofLevel

coordinateResidualWeight :
  (n : Nat) → KMajor.KMajorFactorCoordinate n → BishopReal.ℝ
coordinateResidualWeight n coordinate =
  BishopReal._*_
    (Iterated.natReal (KMajor.divisor coordinate))
    (Exp.bishopExp
      (Rate.residualExponent n (KMajor.residual coordinate)))

coordinateCubicWeight :
  ∀ {n} {nPositive : suc zero ≤ n} →
  Rate.ErdosStepRate n nPositive →
  KMajor.KMajorFactorCoordinate n → BishopReal.ℝ
coordinateCubicWeight {n} rate coordinate =
  let
    pair = KMajor.asPositiveFactorPair coordinate
    stepPositive = FactorResidual.factorStepPositive rate pair
  in
  BishopReal._*_
    (Iterated.natReal (KMajor.divisor coordinate))
    (BishopReal._*_
      (Iterated.powerQ stepPositive (KMajor.divisor coordinate))
      (Exp.bishopExp (Rate.targetExponent n)))

coordinateDivisorNonnegative :
  ∀ {n} (coordinate : KMajor.KMajorFactorCoordinate n) →
  BishopReal.NonNegative (Iterated.natReal (KMajor.divisor coordinate))
coordinateDivisorNonnegative
  (KMajor.kMajorFactorCoordinate copies zero copiesPositive copiesBound
    () divisorBound productBound)
coordinateDivisorNonnegative
  (KMajor.kMajorFactorCoordinate copies (suc divisorPredecessor)
    copiesPositive copiesBound divisorPositive divisorBound productBound) =
  BishopP.pos⇒nonNeg
    (NatPositive.natRealSuccessorPositive divisorPredecessor)

coordinateResidualBelowCubic :
  ∀ {n : Nat} →
  (nPositive : suc 0 ≤ n) →
  (coordinate : KMajor.KMajorFactorCoordinate n) →
  let rate = Rate.canonicalErdosStepRate n nPositive in
  BishopReal._≤_
    (coordinateResidualWeight n coordinate)
    (coordinateCubicWeight rate coordinate)
coordinateResidualBelowCubic {n} nPositive coordinate =
  let
    rate = Rate.canonicalErdosStepRate n nPositive
    pair = KMajor.asPositiveFactorPair coordinate
    expBound =
      FactorExp.factorPairCubicExponentialDomination
        nPositive
        (KMajor.productBound coordinate)
        pair
  in
  BishopP.*-monoˡ-≤-nonNeg
    expBound
    (coordinateDivisorNonnegative coordinate)

partitionErdosBishopKMajorCoordinateDominationLevel : ProofLevel
partitionErdosBishopKMajorCoordinateDominationLevel = machineChecked
