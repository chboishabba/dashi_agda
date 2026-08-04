module DASHI.Physics.Closure.NSTriadKNLuoCanonicalSetZeroAnalyticInputsExact where

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
-- Universe-safe concrete owner for the official periodic NS route.  The
-- repository's actual initial-data, solution and time carriers are selected in
-- Set0.  Consequently the literal equality between the singleton nonlinear
-- state and the selected official solution inhabits the Set0 proposition slot
-- of the historical canonical cutset, without replacing it by an opaque token.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true)
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
import DASHI.Physics.Closure.NSTriadKNLuoPreThresholdCutoffQuantitiesExact as PreQ
import DASHI.Physics.Closure.NSTriadKNLuoPreThresholdPhysicalEnergyTimeExact as PreTime
import DASHI.Physics.Closure.NSTriadKNCanonicalPeriodicLuoContinuationAdvance as Canonical
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact as Physical

record CanonicalSetZeroAnalyticInputs
    (InitialDatum Solution Time : Set)
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

    sourceAbsoluteFluxMatchesPhysicalBridge :
      (shell : Nat) →
      FluxKernel.absoluteHighFlux exactFluxKernel shell tt
      ≡ Physical.absoluteCutoffFlux
          (PreBudget.preBudgetPhysicalBridge data shell)

    commonSchurConstantMatchesPhysicalBridge :
      (shell : Nat) →
      commonSchurConstant
      ≡ Physical.profileSchurConstant
          (PreBudget.preBudgetPhysicalBridge data shell)

    weightedEnergyMatchesPhysicalBridge :
      (shell : Nat) →
      weightedShellEnergy shell
      ≡ Physical.cutoffEnergyMajorant
          (PreBudget.preBudgetPhysicalBridge data shell)

    sourceLowGradientMatchesPhysicalBridge :
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

    section4Inputs :
      Section4.LuoSection4ContinuityInputs
        (PerModeAdapter.perModeEvolutionFromFiniteAssembly
          perModeFiniteInputs)
        Section4Time

    section4UsesSelectedState : Section4.state section4Inputs ≡ tt

    section4AlphaMatchesFixedShift :
      Section4.alpha section4Inputs
      ≡ Uniform.alpha
          (BootstrapConstructor.luoFixedShiftBootstrap
            (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
              fixedShiftCoreInputs fixedShiftBudgetIdentification))

    section4DecayMatchesFixedShiftTarget :
      (shell : Nat) →
      Section4.modeDecay section4Inputs shell
      ≡ Uniform.dyadicDecayTarget
          (BootstrapConstructor.luoFixedShiftBootstrap
            (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
              fixedShiftCoreInputs fixedShiftBudgetIdentification))
          shell

    decodeState : ⊤ → Solution
    selectedStateIsOfficialSolution :
      decodeState tt ≡ PreBudget.solution data

    fixedShiftEnergyMatchesOfficial :
      (shell : Nat) →
      BudgetBootstrap.cutoffEnergy fixedShiftCoreInputs shell
      ≡ PreQ.currentHardHighEnergy
          (PreTime.cutoffQuantities
            (PreBudget.preThresholdEnergyTimeAt data shell))

    fixedShiftDissipationMatchesOfficial :
      (shell : Nat) →
      BudgetBootstrap.cutoffDissipation fixedShiftCoreInputs shell
      ≡ PreQ.physicalDissipation
          (PreTime.cutoffQuantities
            (PreBudget.preThresholdEnergyTimeAt data shell))

    PerModeShellsMatchOfficialLittlewoodPaleyShells : Set
    perModeShellsMatchOfficialLittlewoodPaleyShells :
      PerModeShellsMatchOfficialLittlewoodPaleyShells

open CanonicalSetZeroAnalyticInputs public

derivedTerminalBudgets :
  ∀ {InitialDatum Solution Time : Set}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  CanonicalSetZeroAnalyticInputs InitialDatum Solution Time data →
  PreBudget.DerivedLuoTerminalBudgetFamily data
derivedTerminalBudgets inputs =
  GapBudget.residueGapDerivedTerminalBudgetFamily
    (residueGapBudgetIdentification inputs)

completedOfficialClosure :
  ∀ {InitialDatum Solution Time : Set}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  CanonicalSetZeroAnalyticInputs InitialDatum Solution Time data →
  Completed.OfficialLuoContinuationClosure InitialDatum Solution Time
completedOfficialClosure {data = data} inputs =
  PreBudget.completeOfficialLuoClosure data (derivedTerminalBudgets inputs)

physicalIncrementKernel :
  ∀ {InitialDatum Solution Time : Set}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : CanonicalSetZeroAnalyticInputs
    InitialDatum Solution Time data) →
  FluxKernel.LuoIncrementKernelPhysicalRealization
    (exactFluxKernel inputs) (Space inputs)
physicalIncrementKernel inputs =
  KernelAdapter.officialIncrementKernelPhysicalRealization
    (incrementKernelAnalyticInputs inputs)

perModeEvolution :
  ∀ {InitialDatum Solution Time : Set}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  CanonicalSetZeroAnalyticInputs InitialDatum Solution Time data →
  ModeEvolution.LuoPerModeCommutatorEvolution ⊤ ℚ
perModeEvolution inputs =
  PerModeAdapter.perModeEvolutionFromFiniteAssembly
    (perModeFiniteInputs inputs)

fixedShiftBootstrap :
  ∀ {InitialDatum Solution Time : Set}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  CanonicalSetZeroAnalyticInputs InitialDatum Solution Time data →
  Uniform.LuoFixedShiftUniformBootstrap ℚ
fixedShiftBootstrap inputs =
  BootstrapConstructor.luoFixedShiftBootstrap
    (BudgetBootstrap.fixedShiftBootstrapInputsFromDerivedBudget
      (fixedShiftCoreInputs inputs)
      (fixedShiftBudgetIdentification inputs))

section4Continuity :
  ∀ {InitialDatum Solution Time : Set}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : CanonicalSetZeroAnalyticInputs
    InitialDatum Solution Time data) →
  ModeEvolution.LuoSection4ContinuityBootstrap (perModeEvolution inputs)
section4Continuity inputs =
  Section4.section4ContinuityBootstrap (section4Inputs inputs)

threePieceAdapter :
  ∀ {InitialDatum Solution Time : Set}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : CanonicalSetZeroAnalyticInputs
    InitialDatum Solution Time data) →
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
      sourceAbsoluteFluxMatchesPhysicalBridge inputs shell
  ; commonSchurConstantMatchesBridge = λ shell state →
      commonSchurConstantMatchesPhysicalBridge inputs shell
  ; weightedEnergyMatchesBridge = λ shell state →
      weightedEnergyMatchesPhysicalBridge inputs shell
  ; sourceLowGradientMatchesBridge = λ shell state →
      sourceLowGradientMatchesPhysicalBridge inputs shell
  ; sourceMultiplyIsRationalMultiply = sourceMultiplyIsRationalMultiply inputs
  ; sourceOrderIsRationalOrder = sourceOrderIsRationalOrder inputs
  }

record FixedShiftOfficialCoherence
    {InitialDatum Solution Time : Set}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time}
    (inputs : CanonicalSetZeroAnalyticInputs
      InitialDatum Solution Time data) : Set where
  constructor coherence
  field
    energyCoherence :
      (shell : Nat) →
      BudgetBootstrap.cutoffEnergy (fixedShiftCoreInputs inputs) shell
      ≡ PreQ.currentHardHighEnergy
          (PreTime.cutoffQuantities
            (PreBudget.preThresholdEnergyTimeAt data shell))
    dissipationCoherence :
      (shell : Nat) →
      BudgetBootstrap.cutoffDissipation (fixedShiftCoreInputs inputs) shell
      ≡ PreQ.physicalDissipation
          (PreTime.cutoffQuantities
            (PreBudget.preThresholdEnergyTimeAt data shell))

fixedShiftOfficialCoherence :
  ∀ {InitialDatum Solution Time : Set}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  (inputs : CanonicalSetZeroAnalyticInputs
    InitialDatum Solution Time data) →
  FixedShiftOfficialCoherence inputs
fixedShiftOfficialCoherence inputs =
  coherence
    (fixedShiftEnergyMatchesOfficial inputs)
    (fixedShiftDissipationMatchesOfficial inputs)

canonicalPhysicalRealization :
  ∀ {InitialDatum Solution Time : Set}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  CanonicalSetZeroAnalyticInputs InitialDatum Solution Time data →
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
      decodeState inputs tt ≡ PreBudget.solution data
  ; selectedStateRepresentsOfficialSolution =
      selectedStateIsOfficialSolution inputs
  ; FluxKernelMatchesOfficialProjectedFlux =
      (shell : Nat) →
      FluxKernel.absoluteHighFlux (exactFluxKernel inputs) shell tt
      ≡ Physical.absoluteCutoffFlux
          (PreBudget.preBudgetPhysicalBridge data shell)
  ; fluxKernelMatchesOfficialProjectedFlux =
      sourceAbsoluteFluxMatchesPhysicalBridge inputs
  ; WeightedShellEnergyMatchesOfficialSchurMajorant =
      (shell : Nat) →
      weightedShellEnergy inputs shell
      ≡ Physical.cutoffEnergyMajorant
          (PreBudget.preBudgetPhysicalBridge data shell)
  ; weightedShellEnergyMatchesOfficialSchurMajorant =
      weightedEnergyMatchesPhysicalBridge inputs
  ; FixedShiftDecayMatchesOfficialCutoffEnergy =
      FixedShiftOfficialCoherence inputs
  ; fixedShiftDecayMatchesOfficialCutoffEnergy =
      fixedShiftOfficialCoherence inputs
  ; PerModeShellsMatchOfficialLittlewoodPaleyShells =
      PerModeShellsMatchOfficialLittlewoodPaleyShells inputs
  ; perModeShellsMatchOfficialLittlewoodPaleyShells =
      perModeShellsMatchOfficialLittlewoodPaleyShells inputs
  ; Section4UsesSelectedState =
      ModeEvolution.state (section4Continuity inputs) ≡ tt
  ; section4UsesSelectedState = section4UsesSelectedState inputs
  }

canonicalSourceFaithfulCutset :
  ∀ {InitialDatum Solution Time : Set}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  CanonicalSetZeroAnalyticInputs InitialDatum Solution Time data →
  Canonical.CanonicalPeriodicLuoSourceFaithfulCutset
    InitialDatum Solution Time
canonicalSourceFaithfulCutset inputs =
  Canonical.canonicalPeriodicLuoSourceFaithfulCutset
    (canonicalPhysicalRealization inputs)

setZeroCanonicalOwnerConstructed : Bool
setZeroCanonicalOwnerConstructed = true

setZeroCanonicalOwnerConstructedIsTrue :
  setZeroCanonicalOwnerConstructed ≡ true
setZeroCanonicalOwnerConstructedIsTrue = refl
