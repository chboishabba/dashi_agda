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
-- Build the canonical source-faithful continuation cutset without accepting
-- the desired localized criterion as input. The dependency order is now:
--
--   pre-budget physical data
--     -> residue/gap cutoff majorants
--     -> derived hard terminal-window budgets
--     -> hard/smooth localized criterion
--     -> fixed-b decay bootstrap
--     -> completed official Luo closure
--     -> source-faithful continuation cutset.
--
-- Finite hard-high/full-shell reindexing, equation-(4.2) J-range assembly,
-- fixed-block decay, and final Section-4 composition are all derived. The
-- remaining inputs are the genuinely analytic/semantic obligations: spatial
-- increment Fourier identification, physical pair-kernel equality, physical
-- equation-(4.2) estimates, four Step-1 bounds, mean-value/Gronwall data, and
-- the physical recursion/correction budgets.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
import Data.Rational.Base as ℚBase
open ℚBase using (ℚ)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialPreBudgetDataExact as PreBudget
import DASHI.Physics.Closure.NSTriadKNLuoOfficialContinuationClosureExact as Completed
import DASHI.Physics.Closure.NSTriadKNLuoResidueGapHardWindowBudgetExact as GapBudget
import DASHI.Physics.Closure.NSTriadKNLuoExactFluxKernelDecompositionExact as FluxKernel
import DASHI.Physics.Closure.NSTriadKNLuoOfficialIncrementKernelFullShellAdapterExact as KernelAdapter
import DASHI.Physics.Closure.NSTriadKNLuoThreePiecePhysicalSchurAdapterExact as ThreePiece
import DASHI.Physics.Closure.NSTriadKNLuoPerModeCommutatorEvolutionExact as ModeEvolution
import DASHI.Physics.Closure.NSTriadKNLuoPerModeFiniteAssemblyAdapterExact as PerModeAdapter
import DASHI.Physics.Closure.NSTriadKNLuoSection4ContinuityConstructorExact as Section4Constructor
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftUniformBootstrapExact as Uniform
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftBootstrapConstructorExact as BootstrapConstructor
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftBootstrapFromDerivedBudgetExact as BudgetBootstrap
import DASHI.Physics.Closure.NSTriadKNLuoAlphaThreeHalvesConstantsExact as Alpha
import DASHI.Physics.Closure.NSTriadKNCanonicalPeriodicLuoContinuationAdvance as Canonical
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact as Physical

record OfficialSourceFaithfulNonlinearInputs
    {d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    (data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time) : Setω where
  field
    residueGapBudgetIdentification :
      GapBudget.ResidueGapHardWindowIdentification data

    Tensor Space Contribution : Set

    exactFluxKernel :
      FluxKernel.LuoExactFluxKernelDecomposition ⊤ Tensor ℚ

    incrementKernelAnalyticInputs :
      KernelAdapter.OfficialIncrementKernelAnalyticInputs
        data exactFluxKernel Space Contribution

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

    sourceAbsoluteFluxMatchesPreBudgetBridge :
      (shell : Nat) →
      FluxKernel.absoluteHighFlux exactFluxKernel shell tt
      ≡ Physical.absoluteCutoffFlux
          (PreBudget.preBudgetPhysicalBridge data shell)

    commonSchurConstantMatchesPreBudgetBridge :
      (shell : Nat) →
      commonSchurConstant
      ≡ Physical.profileSchurConstant
          (PreBudget.preBudgetPhysicalBridge data shell)

    weightedEnergyMatchesPreBudgetBridge :
      (shell : Nat) →
      weightedShellEnergy shell
      ≡ Physical.cutoffEnergyMajorant
          (PreBudget.preBudgetPhysicalBridge data shell)

    sourceLowGradientMatchesPreBudgetBridge :
      (shell : Nat) →
      FluxKernel.lowGradientInfinity exactFluxKernel shell tt
      ≡ Physical.lowPassGradientInfinity
          (PreBudget.preBudgetPhysicalBridge data shell)

    sourceMultiplyIsRationalMultiply :
      (left right : ℚ) →
      FluxKernel.multiply exactFluxKernel left right
      ≡ ℚBase._*_ left right

    sourceOrderIsRationalOrder :
      (left right : ℚ) →
      FluxKernel.lessOrEqual exactFluxKernel left right
      ≡ ℚBase._≤_ left right

    perModeFiniteInputs :
      PerModeAdapter.LuoPerModeFinitePhysicalInputs

    fixedShiftCoreInputs :
      BudgetBootstrap.LuoFixedShiftCoreInputs

    fixedShiftBudgetIdentification :
      BudgetBootstrap.FixedShiftBudgetIdentification
        data
        (GapBudget.residueGapDerivedTerminalBudgetFamily
          residueGapBudgetIdentification)
        fixedShiftCoreInputs

    alphaShift : Alpha.FourAlignedLuoShift

    alphaMatchesThreeHalves :
      Uniform.alpha
        (BootstrapConstructor.luoFixedShiftBootstrap
          (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
            fixedShiftCoreInputs fixedShiftBudgetIdentification))
      ≡ Alpha.alphaThreeHalves

    twoMinusAlphaMatchesHalf :
      Uniform.twoMinusAlpha
        (BootstrapConstructor.luoFixedShiftBootstrap
          (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
            fixedShiftCoreInputs fixedShiftBudgetIdentification))
      ≡ Alpha.twoMinusAlpha

    halfCorrectionMatchesQuarter :
      Uniform.halfTwoMinusAlpha
        (BootstrapConstructor.luoFixedShiftBootstrap
          (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
            fixedShiftCoreInputs fixedShiftBudgetIdentification))
      ≡ Alpha.halfCorrection

    correctedExponentMatchesSevenFourths :
      Uniform.correctedShiftExponent
        (BootstrapConstructor.luoFixedShiftBootstrap
          (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
            fixedShiftCoreInputs fixedShiftBudgetIdentification))
      ≡ Alpha.correctedExponent

    blockShiftMatchesFourAligned :
      Uniform.blockShift
        (BootstrapConstructor.luoFixedShiftBootstrap
          (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
            fixedShiftCoreInputs fixedShiftBudgetIdentification))
      ≡ Alpha.blockShift alphaShift

    correctedCoefficientMatchesFourAligned :
      Uniform.correctedShiftCoefficient
        (BootstrapConstructor.luoFixedShiftBootstrap
          (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
            fixedShiftCoreInputs fixedShiftBudgetIdentification))
      ≡ Alpha.correctedShiftCoefficient alphaShift

    alphaAboveOneEntry :
      Uniform.LuoAlphaAboveOneRegularityEntry
        (BootstrapConstructor.luoFixedShiftBootstrap
          (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
            fixedShiftCoreInputs fixedShiftBudgetIdentification))

    Section4Time : Set

    section4ContinuityInputs :
      Section4Constructor.LuoSection4ContinuityInputs
        (PerModeAdapter.perModeEvolutionFromFiniteAssembly
          perModeFiniteInputs)
        Section4Time

    section4UsesSelectedState :
      Section4Constructor.state section4ContinuityInputs ≡ tt

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

derivedTerminalBudgets :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : OfficialSourceFaithfulNonlinearInputs data) →
  PreBudget.DerivedLuoTerminalBudgetFamily data
derivedTerminalBudgets inputs =
  GapBudget.residueGapDerivedTerminalBudgetFamily
    (residueGapBudgetIdentification inputs)

completedOfficialClosure :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  OfficialSourceFaithfulNonlinearInputs data →
  Completed.OfficialLuoContinuationClosure InitialDatum Solution Time
completedOfficialClosure {data = data} inputs =
  PreBudget.completeOfficialLuoClosure data
    (derivedTerminalBudgets inputs)

officialPhysicalIncrementKernel :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : OfficialSourceFaithfulNonlinearInputs data) →
  FluxKernel.LuoIncrementKernelPhysicalRealization
    (exactFluxKernel inputs) (Space inputs)
officialPhysicalIncrementKernel inputs =
  KernelAdapter.officialIncrementKernelPhysicalRealization
    (incrementKernelAnalyticInputs inputs)

officialPerModeEvolution :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : OfficialSourceFaithfulNonlinearInputs data) →
  ModeEvolution.LuoPerModeCommutatorEvolution ⊤ ℚ
officialPerModeEvolution inputs =
  PerModeAdapter.perModeEvolutionFromFiniteAssembly
    (perModeFiniteInputs inputs)

officialFixedShiftBootstrap :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : OfficialSourceFaithfulNonlinearInputs data) →
  Uniform.LuoFixedShiftUniformBootstrap ℚ
officialFixedShiftBootstrap inputs =
  BootstrapConstructor.luoFixedShiftBootstrap
    (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
      (fixedShiftCoreInputs inputs)
      (fixedShiftBudgetIdentification inputs))

officialSection4Continuity :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : OfficialSourceFaithfulNonlinearInputs data) →
  ModeEvolution.LuoSection4ContinuityBootstrap
    (officialPerModeEvolution inputs)
officialSection4Continuity inputs =
  Section4Constructor.section4ContinuityBootstrap
    (section4ContinuityInputs inputs)

officialThreePieceAdapter :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : OfficialSourceFaithfulNonlinearInputs data) →
  ThreePiece.LuoThreePiecePhysicalSchurAdapter
    (exactFluxKernel inputs)
officialThreePieceAdapter {data = data} inputs = record
  { bridgeAt = λ shell state →
      PreBudget.preBudgetPhysicalBridge data shell
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
      sourceAbsoluteFluxMatchesPreBudgetBridge inputs shell
  ; commonSchurConstantMatchesBridge = λ shell state →
      commonSchurConstantMatchesPreBudgetBridge inputs shell
  ; weightedEnergyMatchesBridge = λ shell state →
      weightedEnergyMatchesPreBudgetBridge inputs shell
  ; sourceLowGradientMatchesBridge = λ shell state →
      sourceLowGradientMatchesPreBudgetBridge inputs shell
  ; sourceMultiplyIsRationalMultiply =
      sourceMultiplyIsRationalMultiply inputs
  ; sourceOrderIsRationalOrder = sourceOrderIsRationalOrder inputs
  }

officialCanonicalPhysicalRealization :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  OfficialSourceFaithfulNonlinearInputs data →
  Canonical.CanonicalPeriodicLuoPhysicalRealization
    InitialDatum Solution Time
officialCanonicalPhysicalRealization {data = data} inputs = record
  { officialClosure = completedOfficialClosure inputs
  ; State = ⊤
  ; Tensor = Tensor inputs
  ; Space = Space inputs
  ; selectedState = tt
  ; exactFluxKernel = exactFluxKernel inputs
  ; physicalIncrementKernel = officialPhysicalIncrementKernel inputs
  ; threePiecePhysicalSchurAdapter = officialThreePieceAdapter inputs
  ; perModeEvolution = officialPerModeEvolution inputs
  ; fixedShiftBootstrap = officialFixedShiftBootstrap inputs
  ; alphaAboveOneEntry = alphaAboveOneEntry inputs
  ; section4Continuity = officialSection4Continuity inputs
  ; SelectedStateRepresentsOfficialSolution =
      SelectedStateRepresentsOfficialSolution inputs
  ; selectedStateRepresentsOfficialSolution =
      selectedStateRepresentsOfficialSolution inputs
  ; FluxKernelMatchesOfficialProjectedFlux =
      (shell : Nat) →
      FluxKernel.absoluteHighFlux (exactFluxKernel inputs) shell tt
      ≡ Physical.absoluteCutoffFlux
          (PreBudget.preBudgetPhysicalBridge data shell)
  ; fluxKernelMatchesOfficialProjectedFlux =
      sourceAbsoluteFluxMatchesPreBudgetBridge inputs
  ; WeightedShellEnergyMatchesOfficialSchurMajorant =
      (shell : Nat) →
      weightedShellEnergy inputs shell
      ≡ Physical.cutoffEnergyMajorant
          (PreBudget.preBudgetPhysicalBridge data shell)
  ; weightedShellEnergyMatchesOfficialSchurMajorant =
      weightedEnergyMatchesPreBudgetBridge inputs
  ; FixedShiftDecayMatchesOfficialCutoffEnergy =
      FixedShiftDecayMatchesOfficialCutoffEnergy inputs
  ; fixedShiftDecayMatchesOfficialCutoffEnergy =
      fixedShiftDecayMatchesOfficialCutoffEnergy inputs
  ; PerModeShellsMatchOfficialLittlewoodPaleyShells =
      PerModeShellsMatchOfficialLittlewoodPaleyShells inputs
  ; perModeShellsMatchOfficialLittlewoodPaleyShells =
      perModeShellsMatchOfficialLittlewoodPaleyShells inputs
  ; Section4UsesSelectedState =
      ModeEvolution.state (officialSection4Continuity inputs) ≡ tt
  ; section4UsesSelectedState = section4UsesSelectedState inputs
  }

officialCanonicalSourceFaithfulCutset :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  OfficialSourceFaithfulNonlinearInputs data →
  Canonical.CanonicalPeriodicLuoSourceFaithfulCutset
    InitialDatum Solution Time
officialCanonicalSourceFaithfulCutset inputs =
  Canonical.canonicalPeriodicLuoSourceFaithfulCutset
    (officialCanonicalPhysicalRealization inputs)

nonCircularOfficialSourceFaithfulBuilderConstructed : Bool
nonCircularOfficialSourceFaithfulBuilderConstructed = true

terminalBudgetDerivedFromResidueGap : Bool
terminalBudgetDerivedFromResidueGap = true

localizedCriterionDerivedFromTerminalBudget : Bool
localizedCriterionDerivedFromTerminalBudget = true

finiteIncrementKernelReindexingDerived : Bool
finiteIncrementKernelReindexingDerived = true

finiteEquation42RangeAssemblyDerived : Bool
finiteEquation42RangeAssemblyDerived = true

section4FinalCompositionDerived : Bool
section4FinalCompositionDerived = true

fixedShiftDecayDerivedByBlockInduction : Bool
fixedShiftDecayDerivedByBlockInduction = true

alphaThreeHalvesAndSevenFourthsPinned : Bool
alphaThreeHalvesAndSevenFourthsPinned = true

canonicalOfficialSourceFaithfulInputsInhabited : Bool
canonicalOfficialSourceFaithfulInputsInhabited = false

nonCircularOfficialSourceFaithfulBuilderConstructedIsTrue :
  nonCircularOfficialSourceFaithfulBuilderConstructed ≡ true
nonCircularOfficialSourceFaithfulBuilderConstructedIsTrue = refl

terminalBudgetDerivedFromResidueGapIsTrue :
  terminalBudgetDerivedFromResidueGap ≡ true
terminalBudgetDerivedFromResidueGapIsTrue = refl

localizedCriterionDerivedFromTerminalBudgetIsTrue :
  localizedCriterionDerivedFromTerminalBudget ≡ true
localizedCriterionDerivedFromTerminalBudgetIsTrue = refl

finiteIncrementKernelReindexingDerivedIsTrue :
  finiteIncrementKernelReindexingDerived ≡ true
finiteIncrementKernelReindexingDerivedIsTrue = refl

finiteEquation42RangeAssemblyDerivedIsTrue :
  finiteEquation42RangeAssemblyDerived ≡ true
finiteEquation42RangeAssemblyDerivedIsTrue = refl

section4FinalCompositionDerivedIsTrue :
  section4FinalCompositionDerived ≡ true
section4FinalCompositionDerivedIsTrue = refl

fixedShiftDecayDerivedByBlockInductionIsTrue :
  fixedShiftDecayDerivedByBlockInduction ≡ true
fixedShiftDecayDerivedByBlockInductionIsTrue = refl

alphaThreeHalvesAndSevenFourthsPinnedIsTrue :
  alphaThreeHalvesAndSevenFourthsPinned ≡ true
alphaThreeHalvesAndSevenFourthsPinnedIsTrue = refl

canonicalOfficialSourceFaithfulInputsInhabitedIsFalse :
  canonicalOfficialSourceFaithfulInputsInhabited ≡ false
canonicalOfficialSourceFaithfulInputsInhabitedIsFalse = refl
