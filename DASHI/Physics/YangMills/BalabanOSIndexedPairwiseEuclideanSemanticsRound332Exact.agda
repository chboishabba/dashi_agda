{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanOSIndexedPairwiseEuclideanSemanticsRound332Exact where

------------------------------------------------------------------------
-- ROUND332 / MAKE THE PAIRWISE TIME TRANSLATION THE OS1 TRANSLATION
--
-- R310 deliberately splits physical time/support semantics from boundedness and
-- topology, but its `timeTranslate` field is still an arbitrary function.  The
-- preferred carrier below removes that representation freedom: translated test
-- observables are definitionally produced by the SAME Euclidean-covariance
-- assembly used for OS1.
--
-- What remains physical is explicit and proof-bearing:
--   * which Translation element means integer Euclidean time t;
--   * that the selected T5 support metric reads that displacement as t.
--
-- Projection to R310 is compiler-owned.  No O(4)/OS1 or support theorem is
-- manufactured here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5OS1RotationRestorationExact as OS1
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanArbitraryPairContinuumClusteringRound304Exact as R304
import DASHI.Physics.YangMills.BalabanPairwiseEuclideanSemanticsRound310Exact as R310

record OSIndexedPairwiseEuclideanSemantics
    {Measure TestObservable PhysicalObservable Translation Rotation : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation TestObservable ℚ) : Set₁ where
  field
    decode : PhysicalObservable → TestObservable

    timeTranslation : Nat → Translation
    EuclideanTimeTranslation : Translation → Nat → Set
    timeTranslationMeaning : ∀ time →
      EuclideanTimeTranslation (timeTranslation time) time

    supportDistanceIsTime : ∀ left right time →
      R304.physicalDistance (R296.asDirectT5TwoSourceShell finite)
        (decode left)
        (OS1.translate assembly (timeTranslation time) (decode right))
      ≡ time

open OSIndexedPairwiseEuclideanSemantics public

asR310PairwiseEuclideanTimeSemantics :
  ∀ {Measure TestObservable PhysicalObservable Translation Rotation}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (assembly : OS1.EuclideanCovarianceAssembly
      Translation Rotation TestObservable ℚ) →
  OSIndexedPairwiseEuclideanSemantics
    {PhysicalObservable = PhysicalObservable}
    {dataSet = dataSet} {extension = extension} {finite = finite}
    assembly →
  R310.PairwiseEuclideanTimeSemantics
    {PhysicalObservable = PhysicalObservable}
    {dataSet = dataSet} {extension = extension} {finite = finite}
asR310PairwiseEuclideanTimeSemantics assembly semantics = record
  { R310.PairwiseEuclideanTimeSemantics.decode = decode semantics
  ; R310.PairwiseEuclideanTimeSemantics.timeTranslate =
      λ observable time →
        OS1.translate assembly (timeTranslation semantics time)
          (decode semantics observable)
  ; R310.PairwiseEuclideanTimeSemantics.supportDistanceIsTime =
      supportDistanceIsTime semantics
  }

record Round332Boundary : Set where
  constructor round332-boundary
  field
    arbitraryTimeTranslateCountsAsOS1Translation : Bool
    arbitraryTimeTranslateCountsAsOS1TranslationIsFalse :
      arbitraryTimeTranslateCountsAsOS1Translation ≡ false

    translatedObservableUsesOS1ActionDefinitionally : Bool
    translatedObservableUsesOS1ActionDefinitionallyIsTrue :
      translatedObservableUsesOS1ActionDefinitionally ≡ true

    euclideanTimeTranslationMeaningStillPhysical : Bool
    euclideanTimeTranslationMeaningStillPhysicalIsTrue :
      euclideanTimeTranslationMeaningStillPhysical ≡ true

    supportDistanceMeaningStillPhysical : Bool
    supportDistanceMeaningStillPhysicalIsTrue :
      supportDistanceMeaningStillPhysical ≡ true

    projectionToR310CompilerOwned : Bool
    projectionToR310CompilerOwnedIsTrue :
      projectionToR310CompilerOwned ≡ true

canonicalRound332Boundary : Round332Boundary
canonicalRound332Boundary =
  round332-boundary false refl true refl true refl true refl true refl

round332OSIndexedTimeSemanticsAdapterLevel : ProofLevel
round332OSIndexedTimeSemanticsAdapterLevel = machineChecked

round332EuclideanTimeTranslationMeaningLevel : ProofLevel
round332EuclideanTimeTranslationMeaningLevel = conditional

round332SupportDistanceMeaningLevel : ProofLevel
round332SupportDistanceMeaningLevel = conditional
