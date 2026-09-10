{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanModeSelectedDirectT5ContinuumUpperRound304Exact where

------------------------------------------------------------------------
-- ROUND304 / DIRECT FINITE T5 SHELL -> MODE-SELECTED CONTINUUM UPPER
--
-- R301/R303 consume only the continuum covariance upper at the test index used
-- by the positive spectral component.  Do not construct a whole spectral object
-- merely to obtain that upper.
--
-- The existing direct T5 shell gives, at every cutoff,
--
--   |Cov_n(F,G)| <= (1/4)(1/2)^distance(F,G).
--
-- R278 already gives convergence of the SAME selected covariance magnitude to
-- the continuum covariance magnitude.  Closedness of rational <= therefore
-- compiles the exact mode-selected continuum upper once the selected test pair
-- has physical separation `time`.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanCMP116DirectT5ContinuumClusteringRound284Exact as R284
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceConnectedClusteringRound274Exact as R274
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanQuantitativeSubgapSpectralCoreRound301Exact as R301
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power

record ModeSelectedDirectT5UpperPayment
    {Measure TestObservable Energy Vector : Set}
    (dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ)
    (extension : R278.ScalarCovarianceConvergenceExtension dataSet)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (quantitative : R299.QuantitativePositiveTimeVacuumCyclicity
      TestObservable Vector)
    (family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative))
    (decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family) : Set₁ where
  field
    directShell : R284.DirectT5TwoSourceShell dataSet extension

    selectedPairDistanceIsTime : ∀ observable time →
      R284.physicalDistance directShell
        (R278.left tests (R300.indexFor decomposition observable time))
        (R278.right tests (R300.indexFor decomposition observable time))
      ≡ time

    rationalUpperClosedUnderSelectedLimit :
      (sequence : Nat → ℚ) (target upper : ℚ) →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
      (∀ cutoff → sequence cutoff ≤ upper) →
      target ≤ upper

open ModeSelectedDirectT5UpperPayment public

finiteSelectedUpper :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family}
    (payment : ModeSelectedDirectT5UpperPayment
      dataSet extension tests quantitative family decomposition)
    cutoff observable time →
  R278.connectedCovarianceMagnitude extension
      (Gram.measureSequence dataSet cutoff)
      (R278.left tests (R300.indexFor decomposition observable time))
      (R278.right tests (R300.indexFor decomposition observable time))
  ≤ Shell.quarter * Power.rationalPower Geo.half time
finiteSelectedUpper {tests = tests} {decomposition = decomposition}
    payment cutoff observable time =
  let
    left = R278.left tests (R300.indexFor decomposition observable time)
    right = R278.right tests (R300.indexFor decomposition observable time)
    raw = R274.connectedCovarianceGeometricBound
      (R284.asDirectTwoSourceData (directShell payment)) cutoff left right
  in
  subst
    (λ distance →
      R278.connectedCovarianceMagnitude _
        (Gram.measureSequence _ cutoff) left right
      ≤ Shell.quarter * Power.rationalPower Geo.half distance)
    (selectedPairDistanceIsTime payment observable time)
    raw

continuumSelectedUpper :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family} →
  ModeSelectedDirectT5UpperPayment
    dataSet extension tests quantitative family decomposition →
  R301.ContinuumSelectedCorrelationUpper decomposition
continuumSelectedUpper {dataSet = dataSet} {extension = extension}
    {tests = tests} {decomposition = decomposition} payment observable time =
  rationalUpperClosedUnderSelectedLimit payment
    (λ cutoff →
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff)
        (R278.left tests (R300.indexFor decomposition observable time))
        (R278.right tests (R300.indexFor decomposition observable time)))
    (R278.connectedCovarianceMagnitude extension
      (Gram.continuumMeasure dataSet)
      (R278.left tests (R300.indexFor decomposition observable time))
      (R278.right tests (R300.indexFor decomposition observable time)))
    (Shell.quarter * Power.rationalPower Geo.half time)
    (R278.selectedConnectedCovarianceMagnitudeConverges
      extension tests (R300.indexFor decomposition observable time))
    (λ cutoff → finiteSelectedUpper payment cutoff observable time)

record Round304Boundary : Set where
  constructor round304-boundary
  field
    fullSpectrumNeededForB1Upper : Bool
    fullSpectrumNeededForB1UpperIsFalse : fullSpectrumNeededForB1Upper ≡ false

    independentContinuumClusteringUpperLeaf : Bool
    independentContinuumClusteringUpperLeafIsFalse :
      independentContinuumClusteringUpperLeaf ≡ false

    selectedFiniteToContinuumUpperCompilerOwned : Bool
    selectedFiniteToContinuumUpperCompilerOwnedIsTrue :
      selectedFiniteToContinuumUpperCompilerOwned ≡ true

canonicalRound304Boundary : Round304Boundary
canonicalRound304Boundary = round304-boundary false refl false refl true refl

round304ModeSelectedContinuumUpperCompilerLevel : ProofLevel
round304ModeSelectedContinuumUpperCompilerLevel = machineChecked

round304OrderedLimitAuthorityLevel : ProofLevel
round304OrderedLimitAuthorityLevel = standardImported

-- Physical/source content entering this compiler is exactly the existing direct
-- finite T5 two-source shell plus the selected support-distance=time meaning.
-- On the preferred R296 route the shell itself is paid by the literal absolute
-- two-J source localization theorem.
round304DirectFiniteTwoJSourceShellLevel : ProofLevel
round304DirectFiniteTwoJSourceShellLevel = R284.round284LiteralTwoSourceCMP116ShellLevel
