{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPairwiseEuclideanSemanticsRound310Exact where

------------------------------------------------------------------------
-- ROUND310 / SPLIT G2 INTO PHYSICAL SEMANTICS + TEST ADMISSIBILITY + ORDER CLOSURE
--
-- R304 packages several logically different coordinates inside one
-- `PhysicalPairwiseTimePresentation`.  R278 already proves the connected-
-- covariance convergence algebra after bounded left/right/product tests are
-- supplied.  Therefore none of these coordinates should be mistaken for a new
-- clustering inequality.
--
-- G2a: physical Euclidean-time semantics
--      decode physical observables, translate one observable in Euclidean time,
--      and identify physical support separation with that time displacement.
--
-- G2b: selected-test admissibility
--      the decoded left, translated right and their product are bounded on the
--      exact T5 measure carrier.
--
-- G2c: scalar-order closure
--      one-sided rational upper bounds survive the selected scalar convergence.
--
-- R310 composes exactly these three coordinates into R304.  It does not demote
-- G2a/G2b to standard analysis: they remain same-carrier physical/application
-- obligations until concrete inhabitants are supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5JMagnitudeDirectShellRound296Exact as R296
import DASHI.Physics.YangMills.BalabanArbitraryPairContinuumClusteringRound304Exact as R304

record PairwiseEuclideanTimeSemantics
    {Measure TestObservable PhysicalObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    : Set₁ where
  field
    decode : PhysicalObservable → TestObservable
    timeTranslate : PhysicalObservable → Nat → TestObservable

    supportDistanceIsTime : ∀ left right time →
      R304.physicalDistance (R296.asDirectT5TwoSourceShell finite)
        (decode left) (timeTranslate right time)
      ≡ time

open PairwiseEuclideanTimeSemantics public

record PairwiseBoundedTestAdmissibility
    {Measure TestObservable PhysicalObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (semantics : PairwiseEuclideanTimeSemantics
      {dataSet = dataSet} {extension = extension} {finite = finite})
    : Set₁ where
  field
    leftBounded : ∀ observable →
      Gram.BoundedObservable dataSet (decode semantics observable)

    translatedRightBounded : ∀ observable time →
      Gram.BoundedObservable dataSet (timeTranslate semantics observable time)

    translatedProductBounded : ∀ left right time →
      Gram.BoundedObservable dataSet
        (Gram.multiplyObservable (Gram.operations dataSet)
          (decode semantics left) (timeTranslate semantics right time))

open PairwiseBoundedTestAdmissibility public

record RationalUpperOrderClosure
    {Measure TestObservable : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    : Set₁ where
  field
    upperClosed :
      (sequence : Nat → ℚ) (target upper : ℚ) →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
      (∀ cutoff → sequence cutoff ≤ upper) →
      target ≤ upper

open RationalUpperOrderClosure public

asPhysicalPairwiseTimePresentation :
  ∀ {Measure TestObservable PhysicalObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {finite : R296.ExactT5JMagnitudePresentation dataSet extension}
    (semantics : PairwiseEuclideanTimeSemantics
      {dataSet = dataSet} {extension = extension} {finite = finite}) →
  PairwiseBoundedTestAdmissibility semantics →
  RationalUpperOrderClosure dataSet →
  R304.PhysicalPairwiseTimePresentation dataSet extension finite
asPhysicalPairwiseTimePresentation semantics admissibility orderClosure = record
  { R304.PhysicalPairwiseTimePresentation.decode = decode semantics
  ; R304.PhysicalPairwiseTimePresentation.timeTranslate = timeTranslate semantics
  ; R304.PhysicalPairwiseTimePresentation.leftBounded = leftBounded admissibility
  ; R304.PhysicalPairwiseTimePresentation.translatedRightBounded =
      translatedRightBounded admissibility
  ; R304.PhysicalPairwiseTimePresentation.translatedProductBounded =
      translatedProductBounded admissibility
  ; R304.PhysicalPairwiseTimePresentation.supportDistanceIsTime =
      supportDistanceIsTime semantics
  ; R304.PhysicalPairwiseTimePresentation.orderClosedUnderContinuumLimit =
      upperClosed orderClosure
  }

------------------------------------------------------------------------
-- Boundary / proof-search classification.
------------------------------------------------------------------------

g2ManufacturesNewCorrelationDecay : Bool
g2ManufacturesNewCorrelationDecay = false

physicalTimeSupportSemanticsStillRequired : Bool
physicalTimeSupportSemanticsStillRequired = true

boundedTestAdmissibilityStillRequired : Bool
boundedTestAdmissibilityStillRequired = true

covarianceLimitAlgebraIsNewYMAnalysis : Bool
covarianceLimitAlgebraIsNewYMAnalysis = false

round310PairwisePresentationCompilerLevel : ProofLevel
round310PairwisePresentationCompilerLevel = machineChecked

round310PhysicalTimeSupportSemanticsLevel : ProofLevel
round310PhysicalTimeSupportSemanticsLevel = conditional

round310BoundedTestAdmissibilityLevel : ProofLevel
round310BoundedTestAdmissibilityLevel = conditional

round310ScalarOrderClosureLevel : ProofLevel
round310ScalarOrderClosureLevel = standardImported

round310ConnectedCovarianceLimitCompilerLevel : ProofLevel
round310ConnectedCovarianceLimitCompilerLevel =
  R278.round278ConnectedCovarianceLimitCompilerLevel

g2ManufacturesNewCorrelationDecayIsFalse :
  g2ManufacturesNewCorrelationDecay ≡ false
g2ManufacturesNewCorrelationDecayIsFalse = refl

physicalTimeSupportSemanticsStillRequiredIsTrue :
  physicalTimeSupportSemanticsStillRequired ≡ true
physicalTimeSupportSemanticsStillRequiredIsTrue = refl

boundedTestAdmissibilityStillRequiredIsTrue :
  boundedTestAdmissibilityStillRequired ≡ true
boundedTestAdmissibilityStillRequiredIsTrue = refl

covarianceLimitAlgebraIsNewYMAnalysisIsFalse :
  covarianceLimitAlgebraIsNewYMAnalysis ≡ false
covarianceLimitAlgebraIsNewYMAnalysisIsFalse = refl
