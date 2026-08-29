module DASHI.Mathematics.NumberTheory.PartitionErdosBishopKMajorCoordinateMaskedTermExact where

------------------------------------------------------------------------
-- CERTIFIED K-MAJOR COORDINATE = NONZERO MASKED RECTANGLE CELL
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Relation.Nullary.Decidable.Core using (yes; no)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopCubicRatioWitnessCongruenceExact as RatioCong
import DASHI.Foundations.BishopCubicTranslationIteratedExact as Iterated
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopCubicStepRateExact as Rate
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopFactorPairCubicResidualExact as FactorResidual
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopKMajorCoordinateDominationExact as Coordinate
import DASHI.Mathematics.NumberTheory.PartitionErdosBishopKMajorMaskedKernelExact as Masked
import DASHI.Mathematics.NumberTheory.PartitionErdosKMajorFactorCoordinateExact as KMajor
open import DASHI.Physics.YangMills.CompactLieProofLevel

coordinateCubicIsFullCell :
  ∀ {n} {nPositive : suc zero ≤ n}
    (rate : Rate.ErdosStepRate n nPositive) →
  (coordinate : KMajor.KMajorFactorCoordinate n) →
  BishopReal._≃_
    (Coordinate.coordinateCubicWeight rate coordinate)
    (BishopReal._*_
      (Masked.fullBlockTerm rate
        (KMajor.copiesPredecessor coordinate)
        (divisorPredecessor coordinate))
      (Exp.bishopExp (Rate.targetExponent n)))
  where
  divisorPredecessor : KMajor.KMajorFactorCoordinate n → Nat
  divisorPredecessor
    (KMajor.kMajorFactorCoordinate copies zero copiesPositive copiesBound
      () divisorBound productBound)
  divisorPredecessor
    (KMajor.kMajorFactorCoordinate copies (suc predecessor)
      copiesPositive copiesBound divisorPositive divisorBound productBound) =
    predecessor
coordinateCubicIsFullCell {n} rate
    (KMajor.kMajorFactorCoordinate copies zero copiesPositive copiesBound
      () divisorBound productBound)
coordinateCubicIsFullCell {n} rate
    coordinate@(KMajor.kMajorFactorCoordinate (suc copiesPredecessor)
      (suc divisorPredecessor) copiesPositive copiesBound
      divisorPositive divisorBound productBound) =
  let
    pair = KMajor.asPositiveFactorPair coordinate
    pairPositive = FactorResidual.factorStepPositive rate pair
    blockPositive = Masked.blockStepPositive rate copiesPredecessor
    qPower =
      RatioCong.qPowerWitnessCongruent
        pairPositive blockPositive (suc divisorPredecessor)
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.*-congˡ
      (Iterated.natReal (suc divisorPredecessor))
      (BishopP.*-congʳ
        (Exp.bishopExp (Rate.targetExponent n))
        qPower))
    (solve 3
      (λ v qv target →
        v ⊗ (qv ⊗ target)
        ⊜ (v ⊗ qv) ⊗ target)
      BishopP.≃-refl
      (Iterated.natReal (suc divisorPredecessor))
      (BishopReal.pow
        (Masked.blockRatio rate copiesPredecessor)
        (suc divisorPredecessor))
      (Exp.bishopExp (Rate.targetExponent n)))

coordinateMaskedTermIsFullCell :
  ∀ {n} {nPositive : suc zero ≤ n}
    (rate : Rate.ErdosStepRate n nPositive) →
  (coordinate : KMajor.KMajorFactorCoordinate n) →
  BishopReal._≃_
    (Masked.maskedBlockTerm {n = n} rate
      (KMajor.copiesPredecessor coordinate)
      (divisorPredecessor coordinate))
    (Masked.fullBlockTerm rate
      (KMajor.copiesPredecessor coordinate)
      (divisorPredecessor coordinate))
  where
  divisorPredecessor : KMajor.KMajorFactorCoordinate n → Nat
  divisorPredecessor
    (KMajor.kMajorFactorCoordinate copies zero copiesPositive copiesBound
      () divisorBound productBound)
  divisorPredecessor
    (KMajor.kMajorFactorCoordinate copies (suc predecessor)
      copiesPositive copiesBound divisorPositive divisorBound productBound) =
    predecessor
coordinateMaskedTermIsFullCell {n} rate
    (KMajor.kMajorFactorCoordinate copies zero copiesPositive copiesBound
      () divisorBound productBound)
coordinateMaskedTermIsFullCell {n} rate
    coordinate@(KMajor.kMajorFactorCoordinate (suc copiesPredecessor)
      (suc divisorPredecessor) copiesPositive copiesBound
      divisorPositive divisorBound productBound)
  with (suc copiesPredecessor * suc divisorPredecessor) NatP.≤? n
... | yes _ = BishopP.≃-refl
... | no notBound = ⊥-elim (notBound productBound)

coordinateCubicIsMaskedCellTimesTarget :
  ∀ {n} {nPositive : suc zero ≤ n}
    (rate : Rate.ErdosStepRate n nPositive) →
  (coordinate : KMajor.KMajorFactorCoordinate n) →
  BishopReal._≃_
    (Coordinate.coordinateCubicWeight rate coordinate)
    (BishopReal._*_
      (Masked.maskedBlockTerm {n = n} rate
        (KMajor.copiesPredecessor coordinate)
        (divisorPredecessor coordinate))
      (Exp.bishopExp (Rate.targetExponent n)))
  where
  divisorPredecessor : KMajor.KMajorFactorCoordinate n → Nat
  divisorPredecessor
    (KMajor.kMajorFactorCoordinate copies zero copiesPositive copiesBound
      () divisorBound productBound)
  divisorPredecessor
    (KMajor.kMajorFactorCoordinate copies (suc predecessor)
      copiesPositive copiesBound divisorPositive divisorBound productBound) =
    predecessor
coordinateCubicIsMaskedCellTimesTarget {n} rate coordinate =
  BishopP.≃-trans
    (coordinateCubicIsFullCell rate coordinate)
    (BishopP.*-congʳ
      (Exp.bishopExp (Rate.targetExponent n))
      (BishopP.≃-symm (coordinateMaskedTermIsFullCell rate coordinate)))

partitionErdosBishopKMajorCoordinateMaskedTermLevel : ProofLevel
partitionErdosBishopKMajorCoordinateMaskedTermLevel = machineChecked
