{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSourceFirstWilsonMixedLogCovarianceRound573Exact where

------------------------------------------------------------------------
-- GOAL-1 B1 / ROUND573:
-- NORMALIZED TWO-SOURCE CUMULANT DIRECTLY ON THE R278 CMP119/T5 CARRIER
--
-- Choose the generic moment algebra from the exact selected finite measure:
--
--   expectation      := R278/Gram expectation on measure_k
--   productObservable:= the SAME T5 multiplication
--   multiply         := the SAME scalar multiplication
--   subtract x y     := x + negate(y).
--
-- Then generic connected covariance is definitionally R278's signed covariance
-- value.  The remaining Wilson source theorem is only R551's mixed-log cluster
-- expansion; the remaining magnitude bridge is the existing rational
-- calibration magnitude(x)=|x|.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base as ℚ using (ℚ; ∣_∣)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanWilsonMixedLogClusterExpansionRound551Exact as R551
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark

r278MomentAlgebra :
  ∀ {Measure Observable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable ℚ} →
  R278.ScalarCovarianceConvergenceExtension dataSet →
  Measure →
  Cumulant.TwoSourceMomentAlgebra Observable ℚ
r278MomentAlgebra {dataSet = dataSet} extension measure = record
  { Cumulant.TwoSourceMomentAlgebra.subtract =
      λ left right →
        Gram.add (Gram.operations dataSet)
          left (R278.negate extension right)
  ; Cumulant.TwoSourceMomentAlgebra.multiply =
      Gram.multiply (Gram.operations dataSet)
  ; Cumulant.TwoSourceMomentAlgebra.productObservable =
      Gram.multiplyObservable (Gram.operations dataSet)
  ; Cumulant.TwoSourceMomentAlgebra.expectation =
      Gram.expectation (Gram.operations dataSet) measure
  }

r278ConnectedCovarianceIsGenericCumulant :
  ∀ {Measure Observable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable ℚ}
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    measure left right →
  Cumulant.connectedCovariance
    (r278MomentAlgebra extension measure)
    left right
  ≡
  R278.connectedCovarianceValue extension measure left right
r278ConnectedCovarianceIsGenericCumulant extension measure left right = refl

record SourceFirstWilsonMixedLogClusterData
    {Measure Observable SourceDirection Cluster : Set}
    (dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ)
    (extension :
      R278.ScalarCovarianceConvergenceExtension dataSet)
    : Set₁ where
  field
    sourceCalculus :
      ∀ cutoff →
      Cumulant.NormalizedLogSourceCalculus
        (r278MomentAlgebra extension
          (Gram.measureSequence dataSet cutoff))

    insertionMeaning :
      ∀ cutoff →
      Cumulant.LiteralTwoSourceInsertionMeaning
        (sourceCalculus cutoff)
        SourceDirection

    contributingClusters :
      Nat → Observable → Observable → List Cluster

    clusterWeight :
      Nat → Observable → Observable → Cluster → ℚ

    literalWilsonMixedLogIsConnectedClusterSum :
      ∀ cutoff left right →
      Cumulant.literalMixedSecondLogDerivative
        (insertionMeaning cutoff)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) left)
        (Cumulant.sourceDirectionOf (insertionMeaning cutoff) right)
      ≡
      TwoMark.sumℚ
        (TwoMark.map
          (clusterWeight cutoff left right)
          (contributingClusters cutoff left right))

    magnitudeIsRationalAbsolute :
      ∀ value →
      R278.magnitude extension value ≡ ∣ value ∣

open SourceFirstWilsonMixedLogClusterData public

asR551 :
  ∀ {Measure Observable SourceDirection Cluster dataSet extension} →
  SourceFirstWilsonMixedLogClusterData
    {Measure = Measure} {Observable = Observable}
    {SourceDirection = SourceDirection} {Cluster = Cluster}
    dataSet extension →
  R551.WilsonMixedLogClusterExpansionSource
    Nat Observable SourceDirection Cluster
asR551 {dataSet = dataSet} {extension = extension} source = record
  { R551.WilsonMixedLogClusterExpansionSource.momentAlgebra =
      λ cutoff →
        r278MomentAlgebra extension
          (Gram.measureSequence dataSet cutoff)
  ; R551.WilsonMixedLogClusterExpansionSource.sourceCalculus =
      sourceCalculus source
  ; R551.WilsonMixedLogClusterExpansionSource.insertionMeaning =
      insertionMeaning source
  ; R551.WilsonMixedLogClusterExpansionSource.contributingClusters =
      contributingClusters source
  ; R551.WilsonMixedLogClusterExpansionSource.clusterWeight =
      clusterWeight source
  ; R551.WilsonMixedLogClusterExpansionSource.literalWilsonMixedLogIsConnectedClusterSum =
      literalWilsonMixedLogIsConnectedClusterSum source
  }

genericAbsoluteCovarianceIsR278Magnitude :
  ∀ {Measure Observable SourceDirection Cluster dataSet extension}
    (source :
      SourceFirstWilsonMixedLogClusterData
        {Measure = Measure} {Observable = Observable}
        {SourceDirection = SourceDirection} {Cluster = Cluster}
        dataSet extension)
    cutoff left right →
  ∣ Cumulant.connectedCovariance
      (R551.momentAlgebra (asR551 source) cutoff)
      left right ∣
  ≡
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff)
    left right
genericAbsoluteCovarianceIsR278Magnitude
    {dataSet = dataSet} {extension = extension}
    source cutoff left right
  rewrite r278ConnectedCovarianceIsGenericCumulant
            extension (Gram.measureSequence dataSet cutoff) left right
        | magnitudeIsRationalAbsolute source
            (R278.connectedCovarianceValue extension
              (Gram.measureSequence dataSet cutoff) left right) =
  refl

round573R278MomentAlgebraCompilerLevel : ProofLevel
round573R278MomentAlgebraCompilerLevel = machineChecked

round573ConnectedCovarianceSameObjectLevel : ProofLevel
round573ConnectedCovarianceSameObjectLevel = machineChecked

round573MagnitudeBridgeCompilerLevel : ProofLevel
round573MagnitudeBridgeCompilerLevel = machineChecked

-- Genuine W1 source content remains the Wilson mixed-log cluster expansion.
literalRound573WilsonMixedLogClusterExpansionLevel : ProofLevel
literalRound573WilsonMixedLogClusterExpansionLevel =
  R551.literalRound551WilsonMixedLogClusterExpansionLevel

-- Existing rational carrier calibration, not a new cluster theorem.
literalRound573MagnitudeIsRationalAbsoluteLevel : ProofLevel
literalRound573MagnitudeIsRationalAbsoluteLevel = conditional

round573PrintedJEqualsWilsonRequired : Bool
round573PrintedJEqualsWilsonRequired = false
