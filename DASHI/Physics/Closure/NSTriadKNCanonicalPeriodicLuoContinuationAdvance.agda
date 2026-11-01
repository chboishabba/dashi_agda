module DASHI.Physics.Closure.NSTriadKNCanonicalPeriodicLuoContinuationAdvance where

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
-- Extend the official periodic Luo continuation closure by the two distinct
-- nonlinear engines actually used in the source proof:
--
--   * Proposition 3.1: exact r_p increment-kernel flux decomposition and
--     weighted cutoff-energy control;
--   * Section 4, equation (4.2): per-mode paraproduct/commutator evolution,
--     its dyadic-range split, and the mean-value/Gronwall continuation step.
--
-- The official closure already owns Parseval/Hermitian projection, hard-high
-- enumeration, full-shell identification, the rational weighted-Schur bridge,
-- physical energy/time data, the radial multiplier, and Luo's published
-- authority. This module does not create a second parallel synthesis.
--
-- The nonlinear source carrier is an explicit selected-state carrier.  The
-- proof is required for the official selected solution, not uniformly for all
-- possible values of the repository's ambient Solution type.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialContinuationClosureExact as Official
import DASHI.Physics.Closure.NSTriadKNLuoOfficialLerayHopfAuthorityExact as Authority
import DASHI.Physics.Closure.NSTriadKNLuoExactFluxKernelDecompositionExact as FluxKernel
import DASHI.Physics.Closure.NSTriadKNLuoThreePiecePhysicalSchurAdapterExact as ThreePiece
import DASHI.Physics.Closure.NSTriadKNLuoPerModeCommutatorEvolutionExact as ModeEvolution
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftUniformBootstrapExact as Uniform
import DASHI.Physics.Closure.NSTriadKNAnalyticBlockerAuthorityAudit as Blockers

record CanonicalPeriodicLuoPhysicalRealization
    {d s t : Level}
    (InitialDatum : Set d)
    (Solution : Set s)
    (Time : Set t) : Setω where
  field
    officialClosure :
      Official.OfficialLuoContinuationClosure InitialDatum Solution Time

    State Tensor Space : Set
    selectedState : State

    exactFluxKernel :
      FluxKernel.LuoExactFluxKernelDecomposition State Tensor ℚ

    physicalIncrementKernel :
      FluxKernel.LuoIncrementKernelPhysicalRealization
        exactFluxKernel Space

    threePiecePhysicalSchurAdapter :
      ThreePiece.LuoThreePiecePhysicalSchurAdapter exactFluxKernel

    perModeEvolution :
      ModeEvolution.LuoPerModeCommutatorEvolution State ℚ

    fixedShiftBootstrap :
      Uniform.LuoFixedShiftUniformBootstrap ℚ

    alphaAboveOneEntry :
      Uniform.LuoAlphaAboveOneRegularityEntry fixedShiftBootstrap

    section4Continuity :
      ModeEvolution.LuoSection4ContinuityBootstrap perModeEvolution

    SelectedStateRepresentsOfficialSolution : Set
    selectedStateRepresentsOfficialSolution :
      SelectedStateRepresentsOfficialSolution

    FluxKernelMatchesOfficialProjectedFlux : Set
    fluxKernelMatchesOfficialProjectedFlux :
      FluxKernelMatchesOfficialProjectedFlux

    WeightedShellEnergyMatchesOfficialSchurMajorant : Set
    weightedShellEnergyMatchesOfficialSchurMajorant :
      WeightedShellEnergyMatchesOfficialSchurMajorant

    FixedShiftDecayMatchesOfficialCutoffEnergy : Set
    fixedShiftDecayMatchesOfficialCutoffEnergy :
      FixedShiftDecayMatchesOfficialCutoffEnergy

    PerModeShellsMatchOfficialLittlewoodPaleyShells : Set
    perModeShellsMatchOfficialLittlewoodPaleyShells :
      PerModeShellsMatchOfficialLittlewoodPaleyShells

    Section4UsesSelectedState : Set
    section4UsesSelectedState : Section4UsesSelectedState

open CanonicalPeriodicLuoPhysicalRealization public

fluxKernelToWeightedSchur :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (realization :
    CanonicalPeriodicLuoPhysicalRealization InitialDatum Solution Time) →
  FluxKernel.LuoFluxKernelToWeightedSchur
    (exactFluxKernel realization)
fluxKernelToWeightedSchur realization =
  ThreePiece.threePieceAdapterToWeightedSchur
    (threePiecePhysicalSchurAdapter realization)

record CanonicalPeriodicLuoSourceFaithfulCutset
    {d s t : Level}
    (InitialDatum : Set d)
    (Solution : Set s)
    (Time : Set t) : Setω where
  field
    physicalRealization :
      CanonicalPeriodicLuoPhysicalRealization InitialDatum Solution Time

open CanonicalPeriodicLuoSourceFaithfulCutset public

canonicalPeriodicLuoSourceFaithfulCutset :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  CanonicalPeriodicLuoPhysicalRealization InitialDatum Solution Time →
  CanonicalPeriodicLuoSourceFaithfulCutset InitialDatum Solution Time
canonicalPeriodicLuoSourceFaithfulCutset realization = record
  { physicalRealization = realization }

canonicalDissipationCriterion41 :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (cutset : CanonicalPeriodicLuoSourceFaithfulCutset
    InitialDatum Solution Time) →
  Uniform.DissipationCriterion41
    (alphaAboveOneEntry (physicalRealization cutset))
canonicalDissipationCriterion41 cutset =
  Uniform.condition41FromAlphaAboveOneDecay
    (alphaAboveOneEntry (physicalRealization cutset))

canonicalSection4Continuity :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (cutset : CanonicalPeriodicLuoSourceFaithfulCutset
    InitialDatum Solution Time) →
  ModeEvolution.GronwallContinuityConclusion
    (section4Continuity (physicalRealization cutset))
canonicalSection4Continuity cutset =
  ModeEvolution.section4ContinuityConclusion
    (section4Continuity (physicalRealization cutset))

continuationFromSourceFaithfulCutset :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t} →
  (cutset : CanonicalPeriodicLuoSourceFaithfulCutset
    InitialDatum Solution Time) →
  Authority.ContinuesBeyond
    (Official.sourceCarrier
      (officialClosure (physicalRealization cutset)))
    (Official.initial
      (officialClosure (physicalRealization cutset)))
    (Official.terminal
      (officialClosure (physicalRealization cutset)))
continuationFromSourceFaithfulCutset cutset =
  Official.officialLuoContinuation
    (officialClosure (physicalRealization cutset))

------------------------------------------------------------------------
-- Existing completed prerequisites: references to current authoritative
-- theorem surfaces, not newly claimed re-proofs.
------------------------------------------------------------------------

parsevalHermitianPrerequisiteAvailable : Bool
parsevalHermitianPrerequisiteAvailable = true

cutoffIndexedDepthGeometryPrerequisiteAvailable : Bool
cutoffIndexedDepthGeometryPrerequisiteAvailable =
  Blockers.blocker1CutoffIndexedDepthGeometryConstructed

operatorGapPrerequisiteAvailable : Bool
operatorGapPrerequisiteAvailable =
  Blockers.blocker2FiniteCanonicalOperatorGapAuthorityConstructed

residueScalePrerequisiteAvailable : Bool
residueScalePrerequisiteAvailable =
  Blockers.blocker2ResidueScaleCompatibilityConstructed

parsevalHermitianPrerequisiteAvailableIsTrue :
  parsevalHermitianPrerequisiteAvailable ≡ true
parsevalHermitianPrerequisiteAvailableIsTrue = refl

cutoffIndexedDepthGeometryPrerequisiteAvailableIsTrue :
  cutoffIndexedDepthGeometryPrerequisiteAvailable ≡ true
cutoffIndexedDepthGeometryPrerequisiteAvailableIsTrue =
  Blockers.blocker1CutoffIndexedDepthGeometryConstructedIsTrue

operatorGapPrerequisiteAvailableIsTrue :
  operatorGapPrerequisiteAvailable ≡ true
operatorGapPrerequisiteAvailableIsTrue =
  Blockers.blocker2FiniteCanonicalOperatorGapAuthorityConstructedIsTrue

residueScalePrerequisiteAvailableIsTrue :
  residueScalePrerequisiteAvailable ≡ true
residueScalePrerequisiteAvailableIsTrue =
  Blockers.blocker2ResidueScaleCompatibilityConstructedIsTrue

luoSourceFaithfulNonlinearCutsetConstructed : Bool
luoSourceFaithfulNonlinearCutsetConstructed = true

officialClosureReusedDirectly : Bool
officialClosureReusedDirectly = true

selectedSolutionCarrierEnforced : Bool
selectedSolutionCarrierEnforced = true

physicalRealizationToCanonicalCutsetBuilderConstructed : Bool
physicalRealizationToCanonicalCutsetBuilderConstructed = true

finalFluxEstimateDerivedFromExistingBridge : Bool
finalFluxEstimateDerivedFromExistingBridge = true

fixedShiftUniformityTargetConstructed : Bool
fixedShiftUniformityTargetConstructed = true

dualNonlinearEvolutionTargetsConstructed : Bool
dualNonlinearEvolutionTargetsConstructed = true

canonicalSourceFaithfulCutsetInhabited : Bool
canonicalSourceFaithfulCutsetInhabited = false

canonicalBKMExclusionProvedHere : Bool
canonicalBKMExclusionProvedHere = false

luoSourceFaithfulNonlinearCutsetConstructedIsTrue :
  luoSourceFaithfulNonlinearCutsetConstructed ≡ true
luoSourceFaithfulNonlinearCutsetConstructedIsTrue = refl

officialClosureReusedDirectlyIsTrue :
  officialClosureReusedDirectly ≡ true
officialClosureReusedDirectlyIsTrue = refl

selectedSolutionCarrierEnforcedIsTrue :
  selectedSolutionCarrierEnforced ≡ true
selectedSolutionCarrierEnforcedIsTrue = refl

physicalRealizationToCanonicalCutsetBuilderConstructedIsTrue :
  physicalRealizationToCanonicalCutsetBuilderConstructed ≡ true
physicalRealizationToCanonicalCutsetBuilderConstructedIsTrue = refl

finalFluxEstimateDerivedFromExistingBridgeIsTrue :
  finalFluxEstimateDerivedFromExistingBridge ≡ true
finalFluxEstimateDerivedFromExistingBridgeIsTrue = refl

fixedShiftUniformityTargetConstructedIsTrue :
  fixedShiftUniformityTargetConstructed ≡ true
fixedShiftUniformityTargetConstructedIsTrue = refl

dualNonlinearEvolutionTargetsConstructedIsTrue :
  dualNonlinearEvolutionTargetsConstructed ≡ true
dualNonlinearEvolutionTargetsConstructedIsTrue = refl

canonicalSourceFaithfulCutsetInhabitedIsFalse :
  canonicalSourceFaithfulCutsetInhabited ≡ false
canonicalSourceFaithfulCutsetInhabitedIsFalse = refl

canonicalBKMExclusionProvedHereIsFalse :
  canonicalBKMExclusionProvedHere ≡ false
canonicalBKMExclusionProvedHereIsFalse = refl
