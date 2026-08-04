module DASHI.Physics.Closure.NSTriadKNLuoCanonicalSourceFaithfulRealizationExact where

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
-- Canonical, non-circular and universe-correct source-faithful realization.
-- The dependency order is:
--
--   threshold-free physical data
--     -> residue/gap hard-window budget
--     -> hard/smooth criterion transfer
--     -> fixed-b block induction
--     -> completed official source closure
--     -> exact Section-4 finite assembly and continuity composition
--     -> canonical continuation cutset.
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
import DASHI.Physics.Closure.NSTriadKNLuoSection4ContinuityProofExact as Section4
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftUniformBootstrapExact as Uniform
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftBootstrapConstructorExact as BootstrapConstructor
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftBootstrapFromDerivedBudgetExact as BudgetBootstrap
import DASHI.Physics.Closure.NSTriadKNLuoAlphaThreeHalvesConstantsExact as Alpha
import DASHI.Physics.Closure.NSTriadKNCanonicalPeriodicLuoContinuationAdvance as Canonical
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact as Physical

record CanonicalSourceFaithfulAnalyticInputs
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
      Uniform.alpha fixedShiftBootstrap ≡ Alpha.alphaThreeHalves
      where
      fixedShiftBootstrap =
        BootstrapConstructor.luoFixedShiftBootstrap
          (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
            fixedShiftCoreInputs fixedShiftBudgetIdentification)

    correctedExponentMatchesSevenFourths :
      Uniform.correctedShiftExponent fixedShiftBootstrap
      ≡ Alpha.correctedExponent
      where
      fixedShiftBootstrap =
        BootstrapConstructor.luoFixedShiftBootstrap
          (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
            fixedShiftCoreInputs fixedShiftBudgetIdentification)

    blockShiftMatchesFourAligned :
      Uniform.blockShift fixedShiftBootstrap ≡ Alpha.blockShift alphaShift
      where
      fixedShiftBootstrap =
        BootstrapConstructor.luoFixedShiftBootstrap
          (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
            fixedShiftCoreInputs fixedShiftBudgetIdentification)

    correctedCoefficientMatchesFourAligned :
      Uniform.correctedShiftCoefficient fixedShiftBootstrap
      ≡ Alpha.correctedShiftCoefficient alphaShift
      where
      fixedShiftBootstrap =
        BootstrapConstructor.luoFixedShiftBootstrap
          (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
            fixedShiftCoreInputs fixedShiftBudgetIdentification)

    alphaAboveOneEntry :
      Uniform.LuoAlphaAboveOneRegularityEntry fixedShiftBootstrap
      where
      fixedShiftBootstrap =
        BootstrapConstructor.luoFixedShiftBootstrap
          (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
            fixedShiftCoreInputs fixedShiftBudgetIdentification)

    Section4Time : Set

    section4Inputs :
      Section4.LuoSection4ContinuityInputs
        (PerModeAdapter.perModeEvolutionFromFiniteAssembly
          perModeFiniteInputs)
        Section4Time

    section4UsesSelectedState : Section4.state section4Inputs ≡ tt

    section4AlphaMatchesFixedShift :
      Section4.alpha section4Inputs
      ≡ Uniform.alpha fixedShiftBootstrap
      where
      fixedShiftBootstrap =
        BootstrapConstructor.luoFixedShiftBootstrap
          (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
            fixedShiftCoreInputs fixedShiftBudgetIdentification)

    section4DecayMatchesFixedShiftTarget :
      (shell : Nat) →
      Section4.modeDecay section4Inputs shell
      ≡ Uniform.dyadicDecayTarget fixedShiftBootstrap shell
      where
      fixedShiftBootstrap =
        BootstrapConstructor.luoFixedShiftBootstrap
          (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
            fixedShiftCoreInputs fixedShiftBudgetIdentification)

    SelectedStateRepresentsOfficialSolution : Set
    selectedStateRepresentsOfficialSolution :
      SelectedStateRepresentsOfficialSolution

    FixedShiftQuantitiesMatchOfficialCutoffData : Set
    fixedShiftQuantitiesMatchOfficialCutoffData :
      FixedShiftQuantitiesMatchOfficialCutoffData

    PerModeShellsMatchOfficialLittlewoodPaleyShells : Set
    perModeShellsMatchOfficialLittlewoodPaleyShells :
      PerModeShellsMatchOfficialLittlewoodPaleyShells

open CanonicalSourceFaithfulAnalyticInputs public

derivedTerminalBudgets :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  CanonicalSourceFaithfulAnalyticInputs data →
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
  CanonicalSourceFaithfulAnalyticInputs data →
  Completed.OfficialLuoContinuationClosure InitialDatum Solution Time
completedOfficialClosure {data = data} inputs =
  PreBudget.completeOfficialLuoClosure data (derivedTerminalBudgets inputs)

physicalIncrementKernel :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : CanonicalSourceFaithfulAnalyticInputs data) →
  FluxKernel.LuoIncrementKernelPhysicalRealization
    (exactFluxKernel inputs) (Space inputs)
physicalIncrementKernel inputs =
  KernelAdapter.officialIncrementKernelPhysicalRealization
    (incrementKernelAnalyticInputs inputs)

perModeEvolution :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  CanonicalSourceFaithfulAnalyticInputs data →
  ModeEvolution.LuoPerModeCommutatorEvolution ⊤ ℚ
perModeEvolution inputs =
  PerModeAdapter.perModeEvolutionFromFiniteAssembly
    (perModeFiniteInputs inputs)

fixedShiftBootstrap :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  CanonicalSourceFaithfulAnalyticInputs data →
  Uniform.LuoFixedShiftUniformBootstrap ℚ
fixedShiftBootstrap inputs =
  BootstrapConstructor.luoFixedShiftBootstrap
    (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
      (fixedShiftCoreInputs inputs)
      (fixedShiftBudgetIdentification inputs))

section4Continuity :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : CanonicalSourceFaithfulAnalyticInputs data) →
  ModeEvolution.LuoSection4ContinuityBootstrap (perModeEvolution inputs)
section4Continuity inputs =
  Section4.section4ContinuityBootstrap (section4Inputs inputs)

threePieceAdapter :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : CanonicalSourceFaithfulAnalyticInputs data) →
  ThreePiece.LuoThreePiecePhysicalSchurAdapter (exactFluxKernel inputs)
threePieceAdapter {data = data} inputs = record
  { bridgeAt = λ shell state → PreBudget.preBudgetPhysicalBridge data shell
  ; commonSchurConstant = commonSchurConstant inputs
  ; weightedShellEnergy = λ shell state → weightedShellEnergy inputs shell
  ; sourceEnergySum = λ shell state → sourceEnergySum inputs shell
  ; sourceEnergySumMeaning = λ shell state → sourceEnergySumMeaning inputs shell
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
  ; sourceMultiplyIsRationalMultiply = sourceMultiplyIsRationalMultiply inputs
  ; sourceOrderIsRationalOrder = sourceOrderIsRationalOrder inputs
  }

canonicalPhysicalRealization :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  CanonicalSourceFaithfulAnalyticInputs data →
  Canonical.CanonicalPeriodicLuoPhysicalRealization
    InitialDatum Solution Time
canonicalPhysicalRealization {data = data} inputs = record
  { officialClosure = completedOfficialClosure inputs
  ; State = ⊤
  ; Tensor = Tensor inputs
  ; Space = Space inputs
  ; selectedState = tt
  ; exactFluxKernel = exactFluxKernel inputs
  ; physicalIncrementKernel = physicalIncrementKernel inputs
  ; threePiecePhysicalSchurAdapter = threePieceAdapter inputs
  ; perModeEvolution = perModeEvolution inputs
  ; fixedShiftBootstrap = fixedShiftBootstrap inputs
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
      FixedShiftQuantitiesMatchOfficialCutoffData inputs
  ; fixedShiftDecayMatchesOfficialCutoffEnergy =
      fixedShiftQuantitiesMatchOfficialCutoffData inputs
  ; PerModeShellsMatchOfficialLittlewoodPaleyShells =
      PerModeShellsMatchOfficialLittlewoodPaleyShells inputs
  ; perModeShellsMatchOfficialLittlewoodPaleyShells =
      perModeShellsMatchOfficialLittlewoodPaleyShells inputs
  ; Section4UsesSelectedState =
      ModeEvolution.state (section4Continuity inputs) ≡ tt
  ; section4UsesSelectedState = section4UsesSelectedState inputs
  }

canonicalSourceFaithfulCutset :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  CanonicalSourceFaithfulAnalyticInputs data →
  Canonical.CanonicalPeriodicLuoSourceFaithfulCutset
    InitialDatum Solution Time
canonicalSourceFaithfulCutset inputs =
  Canonical.canonicalPeriodicLuoSourceFaithfulCutset
    (canonicalPhysicalRealization inputs)

canonicalSourceFaithfulBuilderConstructed : Bool
canonicalSourceFaithfulBuilderConstructed = true

canonicalSourceFaithfulAnalyticInputsInhabited : Bool
canonicalSourceFaithfulAnalyticInputsInhabited = false

canonicalSourceFaithfulBuilderConstructedIsTrue :
  canonicalSourceFaithfulBuilderConstructed ≡ true
canonicalSourceFaithfulBuilderConstructedIsTrue = refl

canonicalSourceFaithfulAnalyticInputsInhabitedIsFalse :
  canonicalSourceFaithfulAnalyticInputsInhabited ≡ false
canonicalSourceFaithfulAnalyticInputsInhabitedIsFalse = refl
