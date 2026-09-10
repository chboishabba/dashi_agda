{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanArbitraryPairContinuumClusteringRound304Exact where

------------------------------------------------------------------------
-- ROUND304 / ARBITRARY-PAIR FINITE T5 SHELL -> CONTINUUM CLUSTERING
--
-- The standard OS/spectral mass-gap route consumes a genuine two-observable
-- Euclidean-time clustering theorem.  Do not fake that consumer by encoding a
-- pair into one opaque spectral observable.
--
-- R296 already gives the finite shell bound for arbitrary left/right T5
-- observables.  R278 already gives covariance-magnitude convergence whenever
-- left, right and their product are bounded.  Therefore the only representation
-- work here is:
--
--   * choose the actual physical observable family;
--   * choose its Euclidean-time translate;
--   * prove the translated pair is in R278's bounded test class;
--   * prove source support distance equals the requested Euclidean time.
--
-- Closedness of <= under the selected scalar convergence is standard topology.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanCMP116DirectT5ContinuumClusteringRound284Exact as R284
import DASHI.Physics.YangMills.BalabanClayOneSidedCorrelationLimitRound276Exact as R276
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power

record PhysicalPairwiseTimePresentation
    {Measure TestObservable PhysicalObservable : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (finite : R296.ExactT5JMagnitudePresentation dataSet extension) : Set₁ where
  field
    decode : PhysicalObservable → TestObservable
    timeTranslate : PhysicalObservable → Nat → TestObservable

    leftBounded : ∀ observable →
      Gram.BoundedObservable dataSet (decode observable)

    translatedRightBounded : ∀ observable time →
      Gram.BoundedObservable dataSet (timeTranslate observable time)

    translatedProductBounded : ∀ left right time →
      Gram.BoundedObservable dataSet
        (Gram.multiplyObservable (Gram.operations dataSet)
          (decode left) (timeTranslate right time))

    supportDistanceIsTime : ∀ left right time →
      R284.physicalDistance (R296.asDirectT5TwoSourceShell finite)
        (decode left) (timeTranslate right time)
      ≡ time

    orderClosedUnderContinuumLimit :
      (sequence : Nat → ℚ) (target upper : ℚ) →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
      (∀ cutoff → sequence cutoff ≤ upper) →
      target ≤ upper

open PhysicalPairwiseTimePresentation public

pairTests :
  ∀ {Measure TestObservable PhysicalObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension} →
  PhysicalPairwiseTimePresentation dataSet extension finite →
  PhysicalObservable → PhysicalObservable → Nat →
  R278.SelectedConnectedCovarianceTests dataSet
pairTests presentation left right time = record
  { R278.SelectedConnectedCovarianceTests.Index = ⊤
  ; R278.SelectedConnectedCovarianceTests.left = λ _ → decode presentation left
  ; R278.SelectedConnectedCovarianceTests.right =
      λ _ → timeTranslate presentation right time
  ; R278.SelectedConnectedCovarianceTests.leftBounded =
      λ _ → leftBounded presentation left
  ; R278.SelectedConnectedCovarianceTests.rightBounded =
      λ _ → translatedRightBounded presentation right time
  ; R278.SelectedConnectedCovarianceTests.productBounded =
      λ _ → translatedProductBounded presentation left right time
  }

finitePairCorrelation :
  ∀ {Measure TestObservable PhysicalObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension} →
  PhysicalPairwiseTimePresentation dataSet extension finite →
  Nat → PhysicalObservable → PhysicalObservable → Nat → ℚ
finitePairCorrelation {dataSet = dataSet} {extension = extension}
    presentation cutoff left right time =
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff)
    (decode presentation left)
    (timeTranslate presentation right time)

continuumPairCorrelation :
  ∀ {Measure TestObservable PhysicalObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension} →
  PhysicalPairwiseTimePresentation dataSet extension finite →
  PhysicalObservable → PhysicalObservable → Nat → ℚ
continuumPairCorrelation {dataSet = dataSet} {extension = extension}
    presentation left right time =
  R278.connectedCovarianceMagnitude extension
    (Gram.continuumMeasure dataSet)
    (decode presentation left)
    (timeTranslate presentation right time)

pairCorrelationConverges :
  ∀ {Measure TestObservable PhysicalObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (presentation : PhysicalPairwiseTimePresentation dataSet extension finite)
    left right time →
  Gram.Converges (Gram.scalarConvergence dataSet)
    (λ cutoff → finitePairCorrelation presentation cutoff left right time)
    (continuumPairCorrelation presentation left right time)
pairCorrelationConverges {extension = extension}
    presentation left right time =
  R278.selectedConnectedCovarianceMagnitudeConverges extension
    (pairTests presentation left right time) tt

finitePairGeometricUpper :
  ∀ {Measure TestObservable PhysicalObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (presentation : PhysicalPairwiseTimePresentation dataSet extension finite)
    cutoff left right time →
  finitePairCorrelation presentation cutoff left right time
  ≤ Shell.quarter * Power.rationalPower Geo.half time
finitePairGeometricUpper {finite = finite} presentation cutoff left right time =
  let
    shell = R296.asDirectT5TwoSourceShell finite
    raw =
      R284.finiteCovarianceBelowConnectingShell shell cutoff
        (decode presentation left)
        (timeTranslate presentation right time)
    geometric =
      R284.Direct.connectedCovarianceGeometricBound
        (R284.asDirectTwoSourceData shell) cutoff
        (decode presentation left)
        (timeTranslate presentation right time)
  in
  subst
    (λ distance →
      finitePairCorrelation presentation cutoff left right time
      ≤ Shell.quarter * Power.rationalPower Geo.half distance)
    (supportDistanceIsTime presentation left right time)
    geometric

continuumPairGeometricUpper :
  ∀ {Measure TestObservable PhysicalObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (presentation : PhysicalPairwiseTimePresentation dataSet extension finite)
    left right time →
  continuumPairCorrelation presentation left right time
  ≤ Shell.quarter * Power.rationalPower Geo.half time
continuumPairGeometricUpper presentation left right time =
  orderClosedUnderContinuumLimit presentation
    (λ cutoff → finitePairCorrelation presentation cutoff left right time)
    (continuumPairCorrelation presentation left right time)
    (Shell.quarter * Power.rationalPower Geo.half time)
    (pairCorrelationConverges presentation left right time)
    (λ cutoff → finitePairGeometricUpper presentation cutoff left right time)

record Round304Boundary : Set where
  constructor round304-boundary
  field
    oneIndexSpectralObservableUsedAsFakePair : Bool
    oneIndexSpectralObservableUsedAsFakePairIsFalse :
      oneIndexSpectralObservableUsedAsFakePair ≡ false

    arbitraryPairContinuumClusteringNewYMAnalysis : Bool
    arbitraryPairContinuumClusteringNewYMAnalysisIsFalse :
      arbitraryPairContinuumClusteringNewYMAnalysis ≡ false

    physicalTimeTranslationAndDistanceMeaningRequired : Bool
    physicalTimeTranslationAndDistanceMeaningRequiredIsTrue :
      physicalTimeTranslationAndDistanceMeaningRequired ≡ true

    literalAbsoluteJLocalizationStillPhysical : Bool
    literalAbsoluteJLocalizationStillPhysicalIsTrue :
      literalAbsoluteJLocalizationStillPhysical ≡ true

canonicalRound304Boundary : Round304Boundary
canonicalRound304Boundary =
  round304-boundary false refl false refl true refl true refl

round304PairwiseContinuumClusteringCompilerLevel : ProofLevel
round304PairwiseContinuumClusteringCompilerLevel = machineChecked

round304PhysicalTimeTranslationDistanceMeaningLevel : ProofLevel
round304PhysicalTimeTranslationDistanceMeaningLevel = conditional

round304LiteralAbsoluteJLocalizationLevel : ProofLevel
round304LiteralAbsoluteJLocalizationLevel = R296.round296LiteralAbsoluteTwoJLocalizationLevel
