{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanAmplitudeAwareModeSelectedLimitRound342Exact where

------------------------------------------------------------------------
-- ROUND342 / AMPLITUDE-AWARE SELECTED FINITE -> CONTINUUM UPPER
--
-- R304 specializes the finite selected upper to the configured Step-V
-- `(1/4) * (1/2)^t` shell.  The R341 spectral consumer needs only the ratio
-- `1/2`; its amplitude may depend on the selected observable.
--
-- Keep the finite source theorem at its natural normalization:
--
--   Corr_N(O,t) <= C(O) * (1/2)^t
--
-- uniformly in N.  Existing selected covariance convergence and one-sided order
-- closure then transport the same bound to the continuum.  No cluster, source,
-- or spectral theorem is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanAmplitudeAwareModeSelectedSubgapRound341Exact as R341

record ModeSelectedAmplitudeFiniteUpperPayment
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
    fastAmplitude : TestObservable → ℚ
    fastAmplitudeNonnegative : ∀ observable → 0ℚ ≤ fastAmplitude observable

    finiteSelectedUpper : ∀ cutoff observable time →
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff)
        (R278.left tests (R300.indexFor decomposition observable time))
        (R278.right tests (R300.indexFor decomposition observable time))
      ≤ fastAmplitude observable * Power.rationalPower Geo.half time

    rationalUpperClosedUnderSelectedLimit :
      (sequence : Nat → ℚ) (target upper : ℚ) →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
      (∀ cutoff → sequence cutoff ≤ upper) →
      target ≤ upper

open ModeSelectedAmplitudeFiniteUpperPayment public

continuumAmplitudeSelectedUpper :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family}
    (payment : ModeSelectedAmplitudeFiniteUpperPayment
      dataSet extension tests quantitative family decomposition) →
  R341.AmplitudeSelectedCorrelationUpper decomposition (fastAmplitude payment)
continuumAmplitudeSelectedUpper
    {dataSet = dataSet} {extension = extension}
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
    (fastAmplitude payment observable * Power.rationalPower Geo.half time)
    (R278.selectedConnectedCovarianceMagnitudeConverges
      extension tests (R300.indexFor decomposition observable time))
    (λ cutoff → finiteSelectedUpper payment cutoff observable time)

record Round342Boundary : Set where
  constructor round342-boundary
  field
    configuredQuarterShellRequiredForSelectedLimit : Bool
    configuredQuarterShellRequiredForSelectedLimitIsFalse :
      configuredQuarterShellRequiredForSelectedLimit ≡ false

    amplitudePreservedAcrossContinuumLimit : Bool
    amplitudePreservedAcrossContinuumLimitIsTrue :
      amplitudePreservedAcrossContinuumLimit ≡ true

    ratioHalfPreservedAcrossContinuumLimit : Bool
    ratioHalfPreservedAcrossContinuumLimitIsTrue :
      ratioHalfPreservedAcrossContinuumLimit ≡ true

    finiteSelectedUpperStillProofBearing : Bool
    finiteSelectedUpperStillProofBearingIsTrue :
      finiteSelectedUpperStillProofBearing ≡ true

    orderClosureStillRequired : Bool
    orderClosureStillRequiredIsTrue : orderClosureStillRequired ≡ true

    freshYMEstimateIntroduced : Bool
    freshYMEstimateIntroducedIsFalse : freshYMEstimateIntroduced ≡ false

canonicalRound342Boundary : Round342Boundary
canonicalRound342Boundary =
  round342-boundary false refl true refl true refl true refl true refl false refl

round342SelectedLimitCompilerLevel : ProofLevel
round342SelectedLimitCompilerLevel = machineChecked

round342FiniteSelectedUpperLevel : ProofLevel
round342FiniteSelectedUpperLevel = conditional

round342OrderClosureLevel : ProofLevel
round342OrderClosureLevel = standardImported

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
