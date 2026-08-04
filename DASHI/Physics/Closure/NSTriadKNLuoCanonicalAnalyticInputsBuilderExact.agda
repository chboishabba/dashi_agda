module DASHI.Physics.Closure.NSTriadKNLuoCanonicalAnalyticInputsBuilderExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Build the canonical analytic-input record from the irreducible physical
-- leaves while making all canonical choices definitionally:
--
-- * source energy is literally low energy plus high energy;
-- * weighted energy is literally the mature physical Schur majorant;
-- * the selected singleton state decodes directly to the official solution;
-- * fixed-shift energy and dissipation are literally the official physical
--   cutoff quantities.
--
-- This removes duplicated coherence obligations without weakening the
-- remaining PDE estimates. The constructor still requires the physical
-- increment/Fourier data, source flux/gradient identifications, equation-(4.2)
-- data, fixed-shift recursion, Section-4 bounds and Gronwall package.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialPreBudgetDataExact as PreBudget
import DASHI.Physics.Closure.NSTriadKNLuoResidueGapHardWindowBudgetExact as GapBudget
import DASHI.Physics.Closure.NSTriadKNLuoExactFluxKernelDecompositionExact as FluxKernel
import DASHI.Physics.Closure.NSTriadKNLuoOfficialIncrementKernelFullShellAdapterExact as KernelAdapter
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalSourceSchurIdentificationExact as SourceSchur
import DASHI.Physics.Closure.NSTriadKNLuoPerModeFiniteAssemblyAdapterExact as PerMode
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftBootstrapFromDerivedBudgetExact as Fixed
import DASHI.Physics.Closure.NSTriadKNLuoOfficialFixedShiftCoreExact as OfficialFixed
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftBootstrapConstructorExact as FixedConstructor
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftUniformBootstrapExact as Uniform
import DASHI.Physics.Closure.NSTriadKNLuoAlphaThreeHalvesConstantsExact as Alpha
import DASHI.Physics.Closure.NSTriadKNLuoSection4ContinuityProofExact as Section4
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalAnalyticInputsExact as Canonical

record CanonicalAnalyticPhysicalLeaves
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
      FluxKernel.LuoExactFluxKernelDecomposition ⊤ Tensor
        Data.Rational.Base.ℚ

    incrementKernelAnalyticInputs :
      KernelAdapter.OfficialIncrementKernelAnalyticInputs
        data exactFluxKernel Space Contribution

    sourceSchurLeaves :
      SourceSchur.CanonicalSourceSchurPhysicalLeaves
        data Tensor exactFluxKernel

    perModeFiniteInputs :
      PerMode.LuoPerModeFinitePhysicalInputs

    officialFixedShiftLeaves :
      OfficialFixed.OfficialFixedShiftCoreLeaves data

    fixedShiftBudgetIdentification :
      Fixed.FixedShiftBudgetIdentification
        data
        (GapBudget.residueGapDerivedTerminalBudgetFamily
          residueGapBudgetIdentification)
        (OfficialFixed.officialFixedShiftCoreInputs
          officialFixedShiftLeaves)

    alphaShift : Alpha.FourAlignedLuoShift

    alphaMatchesThreeHalves :
      Uniform.alpha
        (FixedConstructor.luoFixedShiftBootstrap
          (Fixed.fixedShiftBootstrapInputsFromDerivedBudget
            (OfficialFixed.officialFixedShiftCoreInputs
              officialFixedShiftLeaves)
            fixedShiftBudgetIdentification))
      ≡ Alpha.alphaThreeHalves

    correctedExponentMatchesSevenFourths :
      Uniform.correctedShiftExponent
        (FixedConstructor.luoFixedShiftBootstrap
          (Fixed.fixedShiftBootstrapInputsFromDerivedBudget
            (OfficialFixed.officialFixedShiftCoreInputs
              officialFixedShiftLeaves)
            fixedShiftBudgetIdentification))
      ≡ Alpha.correctedExponent

    blockShiftMatchesFourAligned :
      Uniform.blockShift
        (FixedConstructor.luoFixedShiftBootstrap
          (Fixed.fixedShiftBootstrapInputsFromDerivedBudget
            (OfficialFixed.officialFixedShiftCoreInputs
              officialFixedShiftLeaves)
            fixedShiftBudgetIdentification))
      ≡ Alpha.blockShift alphaShift

    correctedCoefficientMatchesFourAligned :
      Uniform.correctedShiftCoefficient
        (FixedConstructor.luoFixedShiftBootstrap
          (Fixed.fixedShiftBootstrapInputsFromDerivedBudget
            (OfficialFixed.officialFixedShiftCoreInputs
              officialFixedShiftLeaves)
            fixedShiftBudgetIdentification))
      ≡ Alpha.correctedShiftCoefficient alphaShift

    alphaAboveOneEntry :
      Uniform.LuoAlphaAboveOneRegularityEntry
        (FixedConstructor.luoFixedShiftBootstrap
          (Fixed.fixedShiftBootstrapInputsFromDerivedBudget
            (OfficialFixed.officialFixedShiftCoreInputs
              officialFixedShiftLeaves)
            fixedShiftBudgetIdentification))

    Section4Time : Set

    section4Inputs :
      Section4.LuoSection4ContinuityInputs
        (PerMode.perModeEvolutionFromFiniteAssembly perModeFiniteInputs)
        Section4Time

    section4UsesSelectedState :
      Section4.state section4Inputs ≡ tt

    section4AlphaMatchesFixedShift :
      Section4.alpha section4Inputs
      ≡ Uniform.alpha
          (FixedConstructor.luoFixedShiftBootstrap
            (Fixed.fixedShiftBootstrapInputsFromDerivedBudget
              (OfficialFixed.officialFixedShiftCoreInputs
                officialFixedShiftLeaves)
              fixedShiftBudgetIdentification))

    section4DecayMatchesFixedShiftTarget :
      (shell : Nat) →
      Section4.modeDecay section4Inputs shell
      ≡ Uniform.dyadicDecayTarget
          (FixedConstructor.luoFixedShiftBootstrap
            (Fixed.fixedShiftBootstrapInputsFromDerivedBudget
              (OfficialFixed.officialFixedShiftCoreInputs
                officialFixedShiftLeaves)
              fixedShiftBudgetIdentification))
          shell

    PerModeShellsMatchOfficialLittlewoodPaleyShells : Set
    perModeShellsMatchOfficialLittlewoodPaleyShells :
      PerModeShellsMatchOfficialLittlewoodPaleyShells

open CanonicalAnalyticPhysicalLeaves public

canonicalAnalyticInputsFromPhysicalLeaves :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time} →
  CanonicalAnalyticPhysicalLeaves data →
  Canonical.CanonicalAnalyticInputs data
canonicalAnalyticInputsFromPhysicalLeaves {data = data} leaves = record
  { residueGapBudgetIdentification =
      residueGapBudgetIdentification leaves
  ; Tensor = Tensor leaves
  ; Space = Space leaves
  ; Contribution = Contribution leaves
  ; exactFluxKernel = exactFluxKernel leaves
  ; incrementKernelAnalyticInputs =
      incrementKernelAnalyticInputs leaves
  ; commonSchurConstant =
      SourceSchur.commonSchurConstant (sourceSchurLeaves leaves)
  ; weightedShellEnergy =
      SourceSchur.canonicalWeightedShellEnergy (sourceSchurLeaves leaves)
  ; sourceEnergySum =
      SourceSchur.canonicalSourceEnergySum (sourceSchurLeaves leaves)
  ; sourceEnergySumMeaning = λ shell → refl
  ; weightedSchurDominatesSourceEnergy =
      SourceSchur.canonicalSourceEnergyDominatedByWeightedSchur
        (sourceSchurLeaves leaves)
  ; sourceAbsoluteFluxMatchesPhysicalBridge =
      SourceSchur.sourceAbsoluteFluxMatchesPhysicalBridge
        (sourceSchurLeaves leaves)
  ; commonSchurConstantMatchesPhysicalBridge =
      SourceSchur.commonSchurConstantMatchesPhysicalBridge
        (sourceSchurLeaves leaves)
  ; weightedEnergyMatchesPhysicalBridge = λ shell → refl
  ; sourceLowGradientMatchesPhysicalBridge =
      SourceSchur.sourceLowGradientMatchesPhysicalBridge
        (sourceSchurLeaves leaves)
  ; sourceMultiplyIsRationalMultiply =
      SourceSchur.sourceMultiplyIsRationalMultiply
        (sourceSchurLeaves leaves)
  ; sourceOrderIsRationalOrder =
      SourceSchur.sourceOrderIsRationalOrder
        (sourceSchurLeaves leaves)
  ; perModeFiniteInputs = perModeFiniteInputs leaves
  ; fixedShiftCoreInputs =
      OfficialFixed.officialFixedShiftCoreInputs
        (officialFixedShiftLeaves leaves)
  ; fixedShiftBudgetIdentification =
      fixedShiftBudgetIdentification leaves
  ; alphaShift = alphaShift leaves
  ; alphaMatchesThreeHalves = alphaMatchesThreeHalves leaves
  ; correctedExponentMatchesSevenFourths =
      correctedExponentMatchesSevenFourths leaves
  ; blockShiftMatchesFourAligned =
      blockShiftMatchesFourAligned leaves
  ; correctedCoefficientMatchesFourAligned =
      correctedCoefficientMatchesFourAligned leaves
  ; alphaAboveOneEntry = alphaAboveOneEntry leaves
  ; Section4Time = Section4Time leaves
  ; section4Inputs = section4Inputs leaves
  ; section4UsesSelectedState = section4UsesSelectedState leaves
  ; section4AlphaMatchesFixedShift =
      section4AlphaMatchesFixedShift leaves
  ; section4DecayMatchesFixedShiftTarget =
      section4DecayMatchesFixedShiftTarget leaves
  ; decodeState = λ _ → PreBudget.solution data
  ; selectedStateIsOfficialSolution = refl
  ; fixedShiftEnergyMatchesOfficial =
      OfficialFixed.officialFixedShiftEnergyMeaning
        (officialFixedShiftLeaves leaves)
  ; fixedShiftDissipationMatchesOfficial =
      OfficialFixed.officialFixedShiftDissipationMeaning
        (officialFixedShiftLeaves leaves)
  ; PerModeShellsMatchOfficialLittlewoodPaleyShells =
      PerModeShellsMatchOfficialLittlewoodPaleyShells leaves
  ; perModeShellsMatchOfficialLittlewoodPaleyShells =
      perModeShellsMatchOfficialLittlewoodPaleyShells leaves
  }

canonicalSelectedStateCoherenceDefinitional : Bool
canonicalSelectedStateCoherenceDefinitional = true

canonicalFixedShiftCoherenceDefinitional : Bool
canonicalFixedShiftCoherenceDefinitional = true

canonicalAnalyticInputsBuilderConstructed : Bool
canonicalAnalyticInputsBuilderConstructed = true

canonicalSelectedStateCoherenceDefinitionalIsTrue :
  canonicalSelectedStateCoherenceDefinitional ≡ true
canonicalSelectedStateCoherenceDefinitionalIsTrue = refl

canonicalFixedShiftCoherenceDefinitionalIsTrue :
  canonicalFixedShiftCoherenceDefinitional ≡ true
canonicalFixedShiftCoherenceDefinitionalIsTrue = refl

canonicalAnalyticInputsBuilderConstructedIsTrue :
  canonicalAnalyticInputsBuilderConstructed ≡ true
canonicalAnalyticInputsBuilderConstructedIsTrue = refl
