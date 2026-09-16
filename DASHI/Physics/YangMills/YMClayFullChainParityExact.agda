{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayFullChainParityExact where

------------------------------------------------------------------------
-- FULL AGDA CHAIN PARITY FOR THE ACTIVE LEAN YMClay ASSEMBLY
--
-- This owner specializes the generic parity assembly to the actual current
-- Agda source consumer R387/#970.  It therefore exposes, in one theorem, the
-- direct selected mixed-log upper -> selected continuum clustering -> positive
-- transfer-gap core -> common cutoff/OS conclusion chain.
--
-- The energy-form route is exposed in parallel using the finite gap datum
-- constructed by YMClayBoundedFormParityExact.  Literal physical forms,
-- cutoff->continuum transport and the YM/OS same-object weld remain explicit
-- inputs; no status bit or citation is promoted into them.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanContinuumCovarianceSpectrumConstructorRound281Exact as R281
import DASHI.Physics.YangMills.BalabanCMP116R281SourceResponseSameObjectRound342Exact as R342
import DASHI.Physics.YangMills.BalabanCMP116DirectSelectedSpectralUpperRound387Exact as R387
import DASHI.Physics.YangMills.BalabanClayT5ClusteringToTransferGapExact as Gap
import DASHI.Physics.YangMills.BalabanDirectSelectedUpperToGapFinalExact as Final
import DASHI.Physics.YangMills.YMClayBoundedFormParityExact as Form
import DASHI.Physics.YangMills.YMClayMassGapAssemblyParityExact as Assembly

record DirectSelectedSourceClayInputs
    {Measure TestObservable SpectralObservable Energy : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests}
    (ContinuumGap ContinuumHamiltonian Vacuum GapParameter : Set) : Set₁ where
  field
    directSelectedUpper : R387.DirectSelectedSpectralUpper base tests spectrumSource
    selectedLimitClosure : R342.SelectedLimitUpperClosure {dataSet = dataSet}
    positiveCandidateGap :
      Gap.PositiveEnergy
        (R281.asReconstructedClusteringSpectrum spectrumSource)
        (Gap.gapCandidate (R281.asReconstructedClusteringSpectrum spectrumSource))

    commonContinuumOS :
      Assembly.CommonContinuumOSRoute
        (Gap.PositiveTransferGapCore
          (R281.asReconstructedClusteringSpectrum spectrumSource))
        ContinuumGap ContinuumHamiltonian Vacuum GapParameter

open DirectSelectedSourceClayInputs public

directSelectedSourceBuildsMassGapConclusion :
  ∀ {Measure TestObservable SpectralObservable Energy
      ContinuumGap ContinuumHamiltonian Vacuum GapParameter}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {tests : R278.SelectedConnectedCovarianceTests dataSet}
    {spectrumSource : R281.ContinuumCovarianceSpectrumData
      {SpectralObservable = SpectralObservable} {Energy = Energy}
      dataSet extension tests} →
  DirectSelectedSourceClayInputs
    {spectrumSource = spectrumSource}
    ContinuumGap ContinuumHamiltonian Vacuum GapParameter →
  Assembly.MassGapConclusion ContinuumHamiltonian Vacuum GapParameter
directSelectedSourceBuildsMassGapConclusion
    {spectrumSource = spectrumSource} inputs =
  Assembly.commonContinuumOSCompiler
    (commonContinuumOS inputs)
    (Final.directSelectedUpperBuildsPositiveTransferGapCore
      (directSelectedUpper inputs)
      (selectedLimitClosure inputs)
      (positiveCandidateGap inputs))

record BoundedFormClayInputs
    (Hilbert Scalar ContinuumGap ContinuumHamiltonian Vacuum GapParameter : Set) : Set₁ where
  field
    energyRoute : Assembly.EnergyFormRoute Hilbert Scalar
    commonContinuumOS :
      Assembly.CommonContinuumOSRoute
        (Form.FiniteVacuumFormGapDatum Hilbert Scalar)
        ContinuumGap ContinuumHamiltonian Vacuum GapParameter

open BoundedFormClayInputs public

boundedFormBuildsMassGapConclusion :
  ∀ {Hilbert Scalar ContinuumGap ContinuumHamiltonian Vacuum GapParameter} →
  BoundedFormClayInputs
    Hilbert Scalar ContinuumGap ContinuumHamiltonian Vacuum GapParameter →
  Assembly.MassGapConclusion ContinuumHamiltonian Vacuum GapParameter
boundedFormBuildsMassGapConclusion inputs =
  Assembly.massGapOfEnergyForms
    (energyRoute inputs)
    (commonContinuumOS inputs)

fullSourceChainParityCompilerLevel : ProofLevel
fullSourceChainParityCompilerLevel = machineChecked

fullEnergyFormChainParityCompilerLevel : ProofLevel
fullEnergyFormChainParityCompilerLevel = machineChecked

literalDirectSelectedSourceUpperLevel : ProofLevel
literalDirectSelectedSourceUpperLevel = R387.round387DirectSelectedUpperLevel

literalBoundedPhysicalFormLevel : ProofLevel
literalBoundedPhysicalFormLevel = Form.literalPhysicalBoundedEnergyFormLevel

literalCutoffToContinuumLevel : ProofLevel
literalCutoffToContinuumLevel = Assembly.physicalCutoffToContinuumInputsLevel

literalYMOSSameObjectLevel : ProofLevel
literalYMOSSameObjectLevel = Assembly.physicalYMOSSameObjectInputsLevel

fullAgdaClayParityImplemented : Bool
fullAgdaClayParityImplemented = true

fullAgdaClayParityImplementedIsTrue : fullAgdaClayParityImplemented ≡ true
fullAgdaClayParityImplementedIsTrue = refl

unconditionalPhysicalClayProofConstructed : Bool
unconditionalPhysicalClayProofConstructed = false

unconditionalPhysicalClayProofConstructedIsFalse :
  unconditionalPhysicalClayProofConstructed ≡ false
unconditionalPhysicalClayProofConstructedIsFalse = refl
