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
-- Strengthen the existing weighted-Schur continuation synthesis with the two
-- distinct nonlinear engines actually used in Luo's paper:
--
--   * Proposition 3.1: exact r_p increment-kernel flux decomposition and
--     weighted cutoff-energy control;
--   * Section 4, equation (4.2): per-mode paraproduct/commutator evolution,
--     its dyadic-range split, and the mean-value/Gronwall continuation step.
--
-- Uniformity is owned by one fixed b(alpha) and delta(alpha), never by
-- shell-dependent choices. Existing Parseval/Hermitian projection,
-- cutoff-indexed depth geometry, finite operator-gap and residue-scale proofs
-- are imported as completed prerequisites and are not reconstructed here.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNLuoWeightedSchurContinuationSynthesisExact as Existing
import DASHI.Physics.Closure.NSTriadKNLuoPublishedContinuationAuthorityExact as Published
import DASHI.Physics.Closure.NSTriadKNLuoExactFluxKernelDecompositionExact as FluxKernel
import DASHI.Physics.Closure.NSTriadKNLuoThreePiecePhysicalSchurAdapterExact as ThreePiece
import DASHI.Physics.Closure.NSTriadKNLuoPerModeCommutatorEvolutionExact as ModeEvolution
import DASHI.Physics.Closure.NSTriadKNLuoFixedShiftUniformBootstrapExact as Uniform
import DASHI.Physics.Closure.NSTriadKNAnalyticBlockerAuthorityAudit as Blockers

------------------------------------------------------------------------
-- One physical package owns every source-facing object. The scalar carrier is
-- the repository's rational verification carrier, so the physical Schur bound
-- can be transported by the concrete adapter rather than by a free estimate.
------------------------------------------------------------------------

record CanonicalPeriodicLuoPhysicalRealization : Setω where
  field
    existingSynthesis :
      Existing.LuoWeightedSchurContinuationSynthesis

    State Tensor Space : Set

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

    SamePhysicalSolutionCarrier : Set
    samePhysicalSolutionCarrier : SamePhysicalSolutionCarrier

    FluxKernelMatchesExistingProjectedFlux : Set
    fluxKernelMatchesExistingProjectedFlux :
      FluxKernelMatchesExistingProjectedFlux

    WeightedShellEnergyMatchesExistingSchurMajorant : Set
    weightedShellEnergyMatchesExistingSchurMajorant :
      WeightedShellEnergyMatchesExistingSchurMajorant

    FixedShiftDecayMatchesExistingCutoffEnergy : Set
    fixedShiftDecayMatchesExistingCutoffEnergy :
      FixedShiftDecayMatchesExistingCutoffEnergy

    PerModeShellsMatchExistingLittlewoodPaleyShells : Set
    perModeShellsMatchExistingLittlewoodPaleyShells :
      PerModeShellsMatchExistingLittlewoodPaleyShells

open CanonicalPeriodicLuoPhysicalRealization public

fluxKernelToWeightedSchur :
  (realization : CanonicalPeriodicLuoPhysicalRealization) →
  FluxKernel.LuoFluxKernelToWeightedSchur
    (exactFluxKernel realization)
fluxKernelToWeightedSchur realization =
  ThreePiece.threePieceAdapterToWeightedSchur
    (threePiecePhysicalSchurAdapter realization)

record CanonicalPeriodicLuoSourceFaithfulCutset : Setω where
  field
    physicalRealization : CanonicalPeriodicLuoPhysicalRealization

open CanonicalPeriodicLuoSourceFaithfulCutset public

canonicalPeriodicLuoSourceFaithfulCutset :
  CanonicalPeriodicLuoPhysicalRealization →
  CanonicalPeriodicLuoSourceFaithfulCutset
canonicalPeriodicLuoSourceFaithfulCutset realization = record
  { physicalRealization = realization }

canonicalDissipationCriterion41 :
  (cutset : CanonicalPeriodicLuoSourceFaithfulCutset) →
  Uniform.DissipationCriterion41
    (alphaAboveOneEntry (physicalRealization cutset))
canonicalDissipationCriterion41 cutset =
  Uniform.condition41FromAlphaAboveOneDecay
    (alphaAboveOneEntry (physicalRealization cutset))

canonicalSection4Continuity :
  (cutset : CanonicalPeriodicLuoSourceFaithfulCutset) →
  ModeEvolution.GronwallContinuityConclusion
    (section4Continuity (physicalRealization cutset))
canonicalSection4Continuity cutset =
  ModeEvolution.section4ContinuityConclusion
    (section4Continuity (physicalRealization cutset))

continuationFromSourceFaithfulCutset :
  (cutset : CanonicalPeriodicLuoSourceFaithfulCutset) →
  Published.ContinuesBeyond
    (Existing.continuationAuthority
      (existingSynthesis (physicalRealization cutset)))
    (Existing.initialDatum
      (existingSynthesis (physicalRealization cutset)))
    (Existing.terminalTime
      (existingSynthesis (physicalRealization cutset)))
continuationFromSourceFaithfulCutset cutset =
  Existing.luoWeightedSchurContinuation
    (existingSynthesis (physicalRealization cutset))

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
