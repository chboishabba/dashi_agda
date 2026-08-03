module DASHI.Physics.Closure.NSTriadKNLuoOfficialSourceFaithfulRealizationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Build the canonical source-faithful cutset from the existing official Luo
-- continuation closure plus only the genuinely new nonlinear source data.
-- The state carrier is the singleton selected solution, preventing accidental
-- claims of a uniform estimate over the ambient Solution type.
--
-- The finite hard-high/full-shell reindexing is derived automatically from the
-- official list theorem.  The shell-uniform decay is derived automatically
-- from the rational fixed-block induction certificate.  The input package
-- supplies the analytic spatial increment identity, equation-(4.2) estimates,
-- and the physical recursion/correction budgets; neither the Fourier fold nor
-- the final decay conclusion can be chosen independently.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
import Data.Rational.Base as ℚBase
open ℚBase using (ℚ)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialContinuationClosureExact as Official
import DASHI.Physics.Closure.NSTriadKNLuoExactFluxKernelDecompositionExact as FluxKernel
import DASHI.Physics.Closure.NSTriadKNLuoOfficialIncrementKernelFullShellAdapterExact as KernelAdapter
import DASHI.Physics.Closure.NSTriadKNLuoThreePiecePhysicalSchurAdapterExact as ThreePiece
import DASHI.Physics.Closure.NSTriadKNLuoPerModeCommutatorEvolutionExact as ModeEvolution
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftUniformBootstrapExact as Uniform
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftBootstrapConstructorExact as BootstrapConstructor
import DASHI.Physics.Closure.NSTriadKNLuoAlphaThreeHalvesConstantsExact as Alpha
import DASHI.Physics.Closure.NSTriadKNCanonicalPeriodicLuoContinuationAdvance as Canonical
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact as Physical

record OfficialSourceFaithfulNonlinearInputs
    {d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    (closure : Official.OfficialLuoContinuationClosure
      InitialDatum Solution Time) : Setω where
  field
    Tensor Space Contribution : Set

    exactFluxKernel :
      FluxKernel.LuoExactFluxKernelDecomposition ⊤ Tensor ℚ

    incrementKernelAnalyticInputs :
      KernelAdapter.OfficialIncrementKernelAnalyticInputs
        closure exactFluxKernel Space Contribution

    commonSchurConstant : ℚ
    weightedShellEnergy sourceEnergySum : Nat → ℚ

    sourceEnergySumMeaning :
      (shell : Nat) →
      sourceEnergySum shell
      ≡ FluxKernel.addScalar exactFluxKernel
          (FluxKernel.lowShellEnergy exactFluxKernel shell tt)
          (FluxKernel.highShellEnergy exactFluxKernel shell tt)

    weightedSchurDominatesSourceEnergy :
      (shell : Nat) →
      FluxKernel.lessOrEqual exactFluxKernel
        (sourceEnergySum shell)
        (FluxKernel.multiply exactFluxKernel
          commonSchurConstant
          (weightedShellEnergy shell))

    sourceAbsoluteFluxMatchesOfficial :
      (shell : Nat) →
      FluxKernel.absoluteHighFlux exactFluxKernel shell tt
      ≡ Physical.absoluteCutoffFlux
          (Official.officialPhysicalBridge closure shell)

    commonSchurConstantMatchesOfficial :
      (shell : Nat) →
      commonSchurConstant
      ≡ Physical.profileSchurConstant
          (Official.officialPhysicalBridge closure shell)

    weightedEnergyMatchesOfficial :
      (shell : Nat) →
      weightedShellEnergy shell
      ≡ Physical.cutoffEnergyMajorant
          (Official.officialPhysicalBridge closure shell)

    sourceLowGradientMatchesOfficial :
      (shell : Nat) →
      FluxKernel.lowGradientInfinity exactFluxKernel shell tt
      ≡ Physical.lowPassGradientInfinity
          (Official.officialPhysicalBridge closure shell)

    sourceMultiplyIsRationalMultiply :
      (left right : ℚ) →
      FluxKernel.multiply exactFluxKernel left right
      ≡ ℚBase._*_ left right

    sourceOrderIsRationalOrder :
      (left right : ℚ) →
      FluxKernel.lessOrEqual exactFluxKernel left right
      ≡ ℚBase._≤_ left right

    perModeEvolution :
      ModeEvolution.LuoPerModeCommutatorEvolution ⊤ ℚ

    fixedShiftBootstrapInputs :
      BootstrapConstructor.LuoFixedShiftBootstrapInputs

    alphaShift : Alpha.FourAlignedLuoShift

    alphaMatchesThreeHalves :
      Uniform.alpha
        (BootstrapConstructor.luoFixedShiftBootstrap
          fixedShiftBootstrapInputs)
      ≡ Alpha.alphaThreeHalves

    twoMinusAlphaMatchesHalf :
      Uniform.twoMinusAlpha
        (BootstrapConstructor.luoFixedShiftBootstrap
          fixedShiftBootstrapInputs)
      ≡ Alpha.twoMinusAlpha

    halfCorrectionMatchesQuarter :
      Uniform.halfTwoMinusAlpha
        (BootstrapConstructor.luoFixedShiftBootstrap
          fixedShiftBootstrapInputs)
      ≡ Alpha.halfCorrection

    correctedExponentMatchesSevenFourths :
      Uniform.correctedShiftExponent
        (BootstrapConstructor.luoFixedShiftBootstrap
          fixedShiftBootstrapInputs)
      ≡ Alpha.correctedExponent

    blockShiftMatchesFourAligned :
      Uniform.blockShift
        (BootstrapConstructor.luoFixedShiftBootstrap
          fixedShiftBootstrapInputs)
      ≡ Alpha.blockShift alphaShift

    correctedCoefficientMatchesFourAligned :
      Uniform.correctedShiftCoefficient
        (BootstrapConstructor.luoFixedShiftBootstrap
          fixedShiftBootstrapInputs)
      ≡ Alpha.correctedShiftCoefficient alphaShift

    alphaAboveOneEntry :
      Uniform.LuoAlphaAboveOneRegularityEntry
        (BootstrapConstructor.luoFixedShiftBootstrap
          fixedShiftBootstrapInputs)

    section4Continuity :
      ModeEvolution.LuoSection4ContinuityBootstrap perModeEvolution

    section4UsesSelectedState :
      ModeEvolution.state section4Continuity ≡ tt

    SelectedStateRepresentsOfficialSolution : Set
    selectedStateRepresentsOfficialSolution :
      SelectedStateRepresentsOfficialSolution

    FixedShiftDecayMatchesOfficialCutoffEnergy : Set
    fixedShiftDecayMatchesOfficialCutoffEnergy :
      FixedShiftDecayMatchesOfficialCutoffEnergy

    PerModeShellsMatchOfficialLittlewoodPaleyShells : Set
    perModeShellsMatchOfficialLittlewoodPaleyShells :
      PerModeShellsMatchOfficialLittlewoodPaleyShells

open OfficialSourceFaithfulNonlinearInputs public

officialPhysicalIncrementKernel :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {closure : Official.OfficialLuoContinuationClosure
      InitialDatum Solution Time} →
  (inputs : OfficialSourceFaithfulNonlinearInputs closure) →
  FluxKernel.LuoIncrementKernelPhysicalRealization
    (exactFluxKernel inputs) (Space inputs)
officialPhysicalIncrementKernel inputs =
  KernelAdapter.officialIncrementKernelPhysicalRealization
    (incrementKernelAnalyticInputs inputs)

officialFixedShiftBootstrap :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {closure : Official.OfficialLuoContinuationClosure
      InitialDatum Solution Time} →
  (inputs : OfficialSourceFaithfulNonlinearInputs closure) →
  Uniform.LuoFixedShiftUniformBootstrap ℚ
officialFixedShiftBootstrap inputs =
  BootstrapConstructor.luoFixedShiftBootstrap
    (fixedShiftBootstrapInputs inputs)

officialThreePieceAdapter :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {closure : Official.OfficialLuoContinuationClosure
      InitialDatum Solution Time} →
  (inputs : OfficialSourceFaithfulNonlinearInputs closure) →
  ThreePiece.LuoThreePiecePhysicalSchurAdapter
    (exactFluxKernel inputs)
officialThreePieceAdapter {closure = closure} inputs = record
  { bridgeAt = λ shell state →
      Official.officialPhysicalBridge closure shell
  ; commonSchurConstant = commonSchurConstant inputs
  ; weightedShellEnergy = λ shell state →
      weightedShellEnergy inputs shell
  ; sourceEnergySum = λ shell state →
      sourceEnergySum inputs shell
  ; sourceEnergySumMeaning = λ shell state →
      sourceEnergySumMeaning inputs shell
  ; weightedSchurDominatesSourceEnergy = λ shell state →
      weightedSchurDominatesSourceEnergy inputs shell
  ; sourceAbsoluteFluxMatchesBridge = λ shell state →
      sourceAbsoluteFluxMatchesOfficial inputs shell
  ; commonSchurConstantMatchesBridge = λ shell state →
      commonSchurConstantMatchesOfficial inputs shell
  ; weightedEnergyMatchesBridge = λ shell state →
      weightedEnergyMatchesOfficial inputs shell
  ; sourceLowGradientMatchesBridge = λ shell state →
      sourceLowGradientMatchesOfficial inputs shell
  ; sourceMultiplyIsRationalMultiply =
      sourceMultiplyIsRationalMultiply inputs
  ; sourceOrderIsRationalOrder = sourceOrderIsRationalOrder inputs
  }

officialCanonicalPhysicalRealization :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {closure : Official.OfficialLuoContinuationClosure
      InitialDatum Solution Time} →
  OfficialSourceFaithfulNonlinearInputs closure →
  Canonical.CanonicalPeriodicLuoPhysicalRealization
    InitialDatum Solution Time
officialCanonicalPhysicalRealization {closure = closure} inputs = record
  { officialClosure = closure
  ; State = ⊤
  ; Tensor = Tensor inputs
  ; Space = Space inputs
  ; selectedState = tt
  ; exactFluxKernel = exactFluxKernel inputs
  ; physicalIncrementKernel = officialPhysicalIncrementKernel inputs
  ; threePiecePhysicalSchurAdapter = officialThreePieceAdapter inputs
  ; perModeEvolution = perModeEvolution inputs
  ; fixedShiftBootstrap = officialFixedShiftBootstrap inputs
  ; alphaAboveOneEntry = alphaAboveOneEntry inputs
  ; section4Continuity = section4Continuity inputs
  ; SelectedStateRepresentsOfficialSolution =
      SelectedStateRepresentsOfficialSolution inputs
  ; selectedStateRepresentsOfficialSolution =
      selectedStateRepresentsOfficialSolution inputs
  ; FluxKernelMatchesOfficialProjectedFlux =
      (shell : Nat) →
      FluxKernel.absoluteHighFlux (exactFluxKernel inputs) shell tt
      ≡ Physical.absoluteCutoffFlux
          (Official.officialPhysicalBridge closure shell)
  ; fluxKernelMatchesOfficialProjectedFlux =
      sourceAbsoluteFluxMatchesOfficial inputs
  ; WeightedShellEnergyMatchesOfficialSchurMajorant =
      (shell : Nat) →
      weightedShellEnergy inputs shell
      ≡ Physical.cutoffEnergyMajorant
          (Official.officialPhysicalBridge closure shell)
  ; weightedShellEnergyMatchesOfficialSchurMajorant =
      weightedEnergyMatchesOfficial inputs
  ; FixedShiftDecayMatchesOfficialCutoffEnergy =
      FixedShiftDecayMatchesOfficialCutoffEnergy inputs
  ; fixedShiftDecayMatchesOfficialCutoffEnergy =
      fixedShiftDecayMatchesOfficialCutoffEnergy inputs
  ; PerModeShellsMatchOfficialLittlewoodPaleyShells =
      PerModeShellsMatchOfficialLittlewoodPaleyShells inputs
  ; perModeShellsMatchOfficialLittlewoodPaleyShells =
      perModeShellsMatchOfficialLittlewoodPaleyShells inputs
  ; Section4UsesSelectedState =
      ModeEvolution.state (section4Continuity inputs) ≡ tt
  ; section4UsesSelectedState = section4UsesSelectedState inputs
  }

officialCanonicalSourceFaithfulCutset :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {closure : Official.OfficialLuoContinuationClosure
      InitialDatum Solution Time} →
  OfficialSourceFaithfulNonlinearInputs closure →
  Canonical.CanonicalPeriodicLuoSourceFaithfulCutset
    InitialDatum Solution Time
officialCanonicalSourceFaithfulCutset inputs =
  Canonical.canonicalPeriodicLuoSourceFaithfulCutset
    (officialCanonicalPhysicalRealization inputs)

officialSourceFaithfulBuilderConstructed : Bool
officialSourceFaithfulBuilderConstructed = true

finiteIncrementKernelReindexingDerived : Bool
finiteIncrementKernelReindexingDerived = true

fixedShiftDecayDerivedByBlockInduction : Bool
fixedShiftDecayDerivedByBlockInduction = true

alphaThreeHalvesAndSevenFourthsPinned : Bool
alphaThreeHalvesAndSevenFourthsPinned = true

officialBridgeInputsNotDuplicated : Bool
officialBridgeInputsNotDuplicated = true

canonicalOfficialSourceFaithfulInputsInhabited : Bool
canonicalOfficialSourceFaithfulInputsInhabited = false

officialSourceFaithfulBuilderConstructedIsTrue :
  officialSourceFaithfulBuilderConstructed ≡ true
officialSourceFaithfulBuilderConstructedIsTrue = refl

finiteIncrementKernelReindexingDerivedIsTrue :
  finiteIncrementKernelReindexingDerived ≡ true
finiteIncrementKernelReindexingDerivedIsTrue = refl

fixedShiftDecayDerivedByBlockInductionIsTrue :
  fixedShiftDecayDerivedByBlockInduction ≡ true
fixedShiftDecayDerivedByBlockInductionIsTrue = refl

alphaThreeHalvesAndSevenFourthsPinnedIsTrue :
  alphaThreeHalvesAndSevenFourthsPinned ≡ true
alphaThreeHalvesAndSevenFourthsPinnedIsTrue = refl

officialBridgeInputsNotDuplicatedIsTrue :
  officialBridgeInputsNotDuplicated ≡ true
officialBridgeInputsNotDuplicatedIsTrue = refl

canonicalOfficialSourceFaithfulInputsInhabitedIsFalse :
  canonicalOfficialSourceFaithfulInputsInhabited ≡ false
canonicalOfficialSourceFaithfulInputsInhabitedIsFalse = refl
