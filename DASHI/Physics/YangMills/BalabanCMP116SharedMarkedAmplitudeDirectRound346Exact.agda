{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SharedMarkedAmplitudeDirectRound346Exact where

------------------------------------------------------------------------
-- ROUND346 / LITERAL SHARED-MARKED CMP116 -> AMPLITUDE-PARAMETRIC B UPPER
--
-- R344 forced the actual source amplitude
--
--       A_H = (1/4) C_H
--
-- below the historical normalized amplitude 1/4, hence carried C_H <= 1.
-- R345 shows that this normalization is not required by the terminal spectral
-- contradiction: any finite nonnegative A_H multiplying (1/2)^t is fast enough.
--
-- This owner therefore keeps the ACTUAL shared-marked amplitude all the way to
-- the mode-indexed continuum upper.  It also removes the abstract sourceRoot /
-- sourceDistance presentation from R342: the selected theorem is stated directly
-- on R318's literal T5 connecting root and physical support distance.
--
-- Remaining source-facing content:
--   * literal selected CMP116 differentiated localization on the shared hessian
--     mark;
--   * physical support distance of the selected pair equals Euclidean time.
--
-- C_H <= 1 is not a field.  No arbitrary source-distance weld is a field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact as Common
import DASHI.Physics.YangMills.BalabanCMP116CanonicalCommonRadiusRound104Exact as R104
import DASHI.Physics.YangMills.BalabanCMP116CanonicalRadiusToCommonDomainRound114Exact as R114
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116R281ModeSelectedDirectRound341Exact as R341
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact as Geometric
import DASHI.Physics.YangMills.BalabanCMP116TwoSourceTrajectoryRound280Exact as R280
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanQuantitativePositiveTimeCyclicityRound299Exact as R299
import DASHI.Physics.YangMills.BalabanCyclicSubgapNonzeroByConstructionRound297Exact as R297
import DASHI.Physics.YangMills.BalabanPositiveSpectralComponentLowerRound300Exact as R300
import DASHI.Physics.YangMills.BalabanQuantitativeSubgapSpectralCoreRound301Exact as R301
import DASHI.Physics.YangMills.BalabanSubgapGeometricSeparationRound293Exact as R293
import DASHI.Physics.YangMills.BalabanAmplitudeParametricSubgapUpperRound345Exact as R345
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap

record SharedMarkedAmplitudeDirectCMP116Source
    {Measure TestObservable Energy Vector : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (demands : R104.CMP116FiniteNormalizedAnalyticDemands)
    (tests : R278.SelectedConnectedCovarianceTests dataSet)
    (quantitative : R299.QuantitativePositiveTimeVacuumCyclicity
      TestObservable Vector)
    (family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative))
    (decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family)
    : Set₁ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl
      (R318.Scale base) (R318.Volume base) (R318.Root base)

    literalSelectedDifferentiatedLocalization :
      ∀ cutoff observable time →
      let
        index = R300.indexFor decomposition observable time
        left = R278.left tests index
        right = R278.right tests index
        leftJ = Cumulant.sourceDirectionOf (R318.meaning base) left
        rightJ = Cumulant.sourceDirectionOf (R318.meaning base) right
      in
      Common.SourceCoordinateInside
        (R114.canonicalCMP116CommonDomain
          {R318.Scale base} {R318.Volume base} demands)
        (R318.scaleOf base cutoff) (R318.volumeOf base cutoff) →
      R278.magnitude extension
        (Cumulant.literalMixedSecondLogDerivative (R318.meaning base)
          leftJ rightJ cutoff)
      ≤ Shared.markedAnalyticShell shared Shared.hessianMark
          (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
          (R318.connectingRoot base cutoff left right)
          (R318.physicalDistance base left right)

    selectedPhysicalDistanceIsTime : ∀ observable time →
      let
        index = R300.indexFor decomposition observable time
      in
      R318.physicalDistance base
        (R278.left tests index) (R278.right tests index)
      ≡ time

    rationalUpperClosedUnderSelectedLimit :
      (sequence : Nat → ℚ) (target upper : ℚ) →
      Gram.Converges (Gram.scalarConvergence dataSet) sequence target →
      (∀ cutoff → sequence cutoff ≤ upper) →
      target ≤ upper

open SharedMarkedAmplitudeDirectCMP116Source public

fastAmplitude :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family} →
  SharedMarkedAmplitudeDirectCMP116Source
    base demands tests quantitative family decomposition → ℚ
fastAmplitude source =
  Geometric.markedBaseEnergy (shared source) Shared.hessianMark

fastAmplitudeNonnegative :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family}
    (source : SharedMarkedAmplitudeDirectCMP116Source
      base demands tests quantitative family decomposition) →
  0ℚ ≤ fastAmplitude source
fastAmplitudeNonnegative source =
  Geometric.markedBaseEnergyNonnegative (shared source) Shared.hessianMark

finiteSelectedUpper :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family}
    (source : SharedMarkedAmplitudeDirectCMP116Source
      base demands tests quantitative family decomposition) →
  ∀ cutoff observable time →
  let index = R300.indexFor decomposition observable time in
  R278.connectedCovarianceMagnitude extension
    (Gram.measureSequence dataSet cutoff)
    (R278.left tests index) (R278.right tests index)
  ≤ fastAmplitude source * Power.rationalPower Geo.half time
finiteSelectedUpper
    {dataSet = dataSet} {extension = extension} {base = base}
    {demands = demands} {tests = tests} {decomposition = decomposition}
    source cutoff observable time =
  let
    index = R300.indexFor decomposition observable time
    left = R278.left tests index
    right = R278.right tests index
    commonInside =
      Common.sourceCoordinateInside
        (R114.canonicalCMP116CommonDomain
          {R318.Scale base} {R318.Volume base} demands)
        (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
    literalBound = literalSelectedDifferentiatedLocalization source
      cutoff observable time commonInside
    geometric = Geometric.markedAnalyticShellGeometricHalf
      (shared source) Shared.hessianMark
      (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
      (R318.connectingRoot base cutoff left right)
      (R318.physicalDistance base left right)
    mixedLogToCovariance =
      R341.mixedLogMagnitudeIsFiniteSelectedCovarianceMagnitude
        base cutoff left right
    covarianceBelowMarked = subst
      (λ lower → lower ≤ Shared.markedAnalyticShell (shared source)
        Shared.hessianMark
        (R318.scaleOf base cutoff) (R318.volumeOf base cutoff)
        (R318.connectingRoot base cutoff left right)
        (R318.physicalDistance base left right))
      mixedLogToCovariance literalBound
    covarianceBelowGeometric = ℚP.≤-trans covarianceBelowMarked geometric
    atTime = subst
      (λ distance →
        R278.connectedCovarianceMagnitude extension
          (Gram.measureSequence dataSet cutoff) left right
        ≤ fastAmplitude source * Geo.halfPower distance)
      (selectedPhysicalDistanceIsTime source observable time)
      covarianceBelowGeometric
  in
  subst
    (λ power →
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff) left right
      ≤ fastAmplitude source * power)
    (R280.halfPowerIsRationalPower time)
    atTime

continuumSelectedUpper :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family} →
  (source : SharedMarkedAmplitudeDirectCMP116Source
    base demands tests quantitative family decomposition) →
  R345.AmplitudeParametricContinuumSelectedCorrelationUpper
    decomposition (fastAmplitude source)
continuumSelectedUpper
    {dataSet = dataSet} {extension = extension} {tests = tests}
    {decomposition = decomposition} source observable time =
  rationalUpperClosedUnderSelectedLimit source
    (λ cutoff →
      R278.connectedCovarianceMagnitude extension
        (Gram.measureSequence dataSet cutoff)
        (R278.left tests (R300.indexFor decomposition observable time))
        (R278.right tests (R300.indexFor decomposition observable time)))
    (R278.connectedCovarianceMagnitude extension
      (Gram.continuumMeasure dataSet)
      (R278.left tests (R300.indexFor decomposition observable time))
      (R278.right tests (R300.indexFor decomposition observable time)))
    (fastAmplitude source * Power.rationalPower Geo.half time)
    (R278.selectedConnectedCovarianceMagnitudeConverges
      extension tests (R300.indexFor decomposition observable time))
    (λ cutoff → finiteSelectedUpper source cutoff observable time)

directNoPositiveSubgapMode :
  ∀ {Measure TestObservable Energy Vector}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {demands : R104.CMP116FiniteNormalizedAnalyticDemands}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {quantitative : R299.QuantitativePositiveTimeVacuumCyclicity TestObservable Vector}
    {family : R297.ActualNonzeroSubgapFamily
      (R299.asPositiveTimeVacuumCyclicity quantitative)}
    {decomposition : R300.PositiveSpectralComponentDecomposition
      dataSet extension tests quantitative family} →
  R293.RationalGeometricDominance →
  (rates : R301.ModeIndexedSubgapRateSemantics
    dataSet extension tests quantitative family decomposition) →
  (source : SharedMarkedAmplitudeDirectCMP116Source
    base demands tests quantitative family decomposition) →
  ∀ energy (mode : R297.SubgapMode family energy) →
  R301.PositiveEnergy rates energy →
  R301.StrictlyBelow rates energy (R301.gapCandidate rates) →
  Gap.Empty
directNoPositiveSubgapMode dominance rates source =
  R345.noPositiveSubgapModeFromAmplitudeParametricUpper
    dominance rates (fastAmplitude source)
    (fastAmplitudeNonnegative source)
    (continuumSelectedUpper source)

hessianConstantAtMostOneIndependentLeaf : Bool
hessianConstantAtMostOneIndependentLeaf = false

hessianConstantAtMostOneIndependentLeafIsFalse :
  hessianConstantAtMostOneIndependentLeaf ≡ false
hessianConstantAtMostOneIndependentLeafIsFalse = refl

abstractSourceDistanceIndependentLeaf : Bool
abstractSourceDistanceIndependentLeaf = false

abstractSourceDistanceIndependentLeafIsFalse :
  abstractSourceDistanceIndependentLeaf ≡ false
abstractSourceDistanceIndependentLeafIsFalse = refl

literalSelectedLocalizationStillProofBearing : Bool
literalSelectedLocalizationStillProofBearing = true

literalSelectedLocalizationStillProofBearingIsTrue :
  literalSelectedLocalizationStillProofBearing ≡ true
literalSelectedLocalizationStillProofBearingIsTrue = refl

selectedPhysicalDistanceMeaningStillProofBearing : Bool
selectedPhysicalDistanceMeaningStillProofBearing = true

selectedPhysicalDistanceMeaningStillProofBearingIsTrue :
  selectedPhysicalDistanceMeaningStillProofBearing ≡ true
selectedPhysicalDistanceMeaningStillProofBearingIsTrue = refl

record Round346Boundary : Set where
  constructor round346-boundary
  field
    fixedQuarterNormalizationMandatory : Bool
    fixedQuarterNormalizationMandatoryIsFalse :
      fixedQuarterNormalizationMandatory ≡ false
    hessianConstantUpperOneMandatory : Bool
    hessianConstantUpperOneMandatoryIsFalse :
      hessianConstantUpperOneMandatory ≡ false
    sourceNativeDistanceCarrierMandatory : Bool
    sourceNativeDistanceCarrierMandatoryIsFalse :
      sourceNativeDistanceCarrierMandatory ≡ false
    actualT5PhysicalDistanceUsedDirectly : Bool
    actualT5PhysicalDistanceUsedDirectlyIsTrue :
      actualT5PhysicalDistanceUsedDirectly ≡ true
    literalSelectedLocalizationStillPhysical : Bool
    literalSelectedLocalizationStillPhysicalIsTrue :
      literalSelectedLocalizationStillPhysical ≡ true
    selectedDistanceTimeMeaningStillPhysical : Bool
    selectedDistanceTimeMeaningStillPhysicalIsTrue :
      selectedDistanceTimeMeaningStillPhysical ≡ true

canonicalRound346Boundary : Round346Boundary
canonicalRound346Boundary =
  round346-boundary false refl false refl false refl true refl true refl true refl

round346AmplitudeDirectCompilerLevel : ProofLevel
round346AmplitudeDirectCompilerLevel = machineChecked

round346LiteralSelectedLocalizationLevel : ProofLevel
round346LiteralSelectedLocalizationLevel = conditional

round346SelectedPhysicalDistanceMeaningLevel : ProofLevel
round346SelectedPhysicalDistanceMeaningLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
