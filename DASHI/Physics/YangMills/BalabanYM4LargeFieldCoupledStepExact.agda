module DASHI.Physics.YangMills.BalabanYM4LargeFieldCoupledStepExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- Feed the finite rooted large-field contribution into the same error
-- coordinate consumed by CoupledOneStepAnalyticBounds.  If
--
--   K' <= q K + (Epert + ELF),
--   ELF <= 2 a,
--   Epert + 2 a <= (1-q) Kmax,
--
-- then the common Gate-4 theorem consumes E = Epert + 2a and closes the
-- invariant region.  Thus rooted shell summability and strict combined polymer
-- closure are connected on the same rational RG state.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanYM4RGInvariantRegionPhysicalGapExact as RG
import DASHI.Physics.YangMills.BalabanYM4RGCommonBudgetClosureExact as Budget
import DASHI.Physics.YangMills.BalabanYM4LargeFieldContributionSharedSlackExact as LF

record LargeFieldCoupledOneStepData
    (parameters : RG.YM4RGRegionParameters)
    (current next : RG.YM4RGState) : Set where
  field
    contraction perturbativeError largeFieldContribution shellAmplitude : ℚ

    contractionNonnegative : 0ℚ ≤ contraction
    contractionAtMostOne : contraction ≤ 1ℚ

    rawCombinedPolymerStep :
      RG.smallFieldPolymerNorm next
      ≤ contraction * RG.smallFieldPolymerNorm current
        + (perturbativeError + largeFieldContribution)

    largeFieldContributionBound :
      largeFieldContribution ≤ shellAmplitude * Geo.twoℚ

    sharedSlack : LF.SharedPolymerSlackAtStep
    sharedSlackContraction : LF.contraction sharedSlack ≡ contraction
    sharedSlackPerturbative :
      LF.perturbativeError sharedSlack ≡ perturbativeError
    sharedSlackCap :
      LF.smallFieldCap sharedSlack ≡ RG.smallFieldCap parameters
    sharedSlackAmplitude :
      LF.largeFieldAmplitude sharedSlack ≡ shellAmplitude

    couplingNextControlled :
      RG.runningCoupling next ≤ RG.couplingCap parameters
    largeFieldNextControlled :
      RG.largeFieldActivity next ≤ RG.largeFieldCap parameters
    covarianceNextControlled :
      RG.conditionalCovarianceNorm next ≤ RG.covarianceCap parameters
    decayNextNonnegative : 0ℚ ≤ RG.latticeDecayExponent next
    spacingNextNonnegative : 0ℚ ≤ RG.inversePhysicalSpacing next

open LargeFieldCoupledOneStepData public

combinedError :
  ∀ {parameters current next} →
  LargeFieldCoupledOneStepData parameters current next → ℚ
combinedError dataSet =
  perturbativeError dataSet + shellAmplitude dataSet * Geo.twoℚ

rawStepBelowCombinedError :
  ∀ {parameters current next}
    (dataSet : LargeFieldCoupledOneStepData parameters current next) →
  RG.smallFieldPolymerNorm next
  ≤ contraction dataSet * RG.smallFieldPolymerNorm current
    + combinedError dataSet
rawStepBelowCombinedError {current = current} dataSet =
  let
    largePlusPerturbative :
      LargeFieldCoupledOneStepData.perturbativeError dataSet
      + LargeFieldCoupledOneStepData.largeFieldContribution dataSet
      ≤ LargeFieldCoupledOneStepData.perturbativeError dataSet
      + LargeFieldCoupledOneStepData.shellAmplitude dataSet * Geo.twoℚ
    largePlusPerturbative =
      ℚP.+-monoʳ-≤
        (LargeFieldCoupledOneStepData.perturbativeError dataSet)
        (LargeFieldCoupledOneStepData.largeFieldContributionBound dataSet)
  in
  ℚP.≤-trans
    (rawCombinedPolymerStep dataSet)
    (ℚP.+-monoʳ-≤
      (contraction dataSet * RG.smallFieldPolymerNorm current)
      largePlusPerturbative)

combinedErrorFitsSlack :
  ∀ {parameters current next}
    (dataSet : LargeFieldCoupledOneStepData parameters current next) →
  combinedError dataSet
  ≤ (1ℚ - contraction dataSet) * RG.smallFieldCap parameters
combinedErrorFitsSlack {parameters = parameters} dataSet
  rewrite sym (sharedSlackContraction dataSet)
        | sym (sharedSlackPerturbative dataSet)
        | sym (sharedSlackCap dataSet)
        | sym (sharedSlackAmplitude dataSet) =
  LF.combinedErrorFitsInvariantSlack (sharedSlack dataSet)

largeFieldCoupledAnalyticBounds :
  ∀ {parameters current next} →
  LargeFieldCoupledOneStepData parameters current next →
  Budget.CoupledOneStepAnalyticBounds parameters current next
largeFieldCoupledAnalyticBounds dataSet = record
  { contraction = contraction dataSet
  ; error = combinedError dataSet
  ; contractionNonnegative =
      contractionNonnegative dataSet
  ; contractionAtMostOne =
      contractionAtMostOne dataSet
  ; smallFieldOneStep =
      rawStepBelowCombinedError dataSet
  ; perturbativeErrorFitsSlack =
      combinedErrorFitsSlack dataSet
  ; couplingNextControlled =
      couplingNextControlled dataSet
  ; largeFieldNextControlled =
      largeFieldNextControlled dataSet
  ; covarianceNextControlled =
      covarianceNextControlled dataSet
  ; decayNextNonnegative =
      decayNextNonnegative dataSet
  ; spacingNextNonnegative =
      spacingNextNonnegative dataSet
  }

largeFieldCoupledStepPreservesRegion :
  ∀ {parameters current next} →
  RG.InYM4RGInvariantRegion parameters current →
  LargeFieldCoupledOneStepData parameters current next →
  RG.InYM4RGInvariantRegion parameters next
largeFieldCoupledStepPreservesRegion currentRegion dataSet =
  Budget.coupledOneStepPreservesAnalyticRegion
    currentRegion
    (largeFieldCoupledAnalyticBounds dataSet)

largeFieldToSharedRGErrorLevel : ProofLevel
largeFieldToSharedRGErrorLevel = machineChecked

largeFieldCoupledRegionClosureLevel : ProofLevel
largeFieldCoupledRegionClosureLevel = machineChecked
