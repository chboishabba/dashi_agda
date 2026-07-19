module DASHI.Analysis.EisensteinTuringModeAnalogyBoundary where

------------------------------------------------------------------------
-- Structural analogy boundary.
--
-- Turing patterning and Eisenstein-series constructions both organise
-- constrained mode geometry, but by different mechanisms:
--   * instability selection in a coupled field,
--   * symmetry-orbit summation in a modular/lattice carrier.
-- No mathematical identity between those mechanisms is asserted.

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Biology.TuringPatternRegimeSurface using
  ( TuringPatternFamily )
open import DASHI.Cognition.ModeGeometrySurface using
  ( ModeGeometryLane
  ; turingReactionDiffusionLane
  ; eisensteinSymmetrySummationLane
  )

record SymmetrySummedModeGeometry : Set₁ where
  constructor symmetrySummedModeGeometry
  field
    Carrier : Set
    SymmetryGroup : Set
    OrbitIndex : Set
    HarmonicMode : Set
    Coefficient : HarmonicMode → Set
    orbitSummationLaw : Set
    symmetryConstraint : Set
    observableHarmonicGeometry : Set

record InstabilitySelectedModeGeometry : Set₁ where
  constructor instabilitySelectedModeGeometry
  field
    CarrierField : Set
    CandidateMode : Set
    selectedFamily : TuringPatternFamily
    dispersionRelation : Set
    unstableBand : CandidateMode → Set
    amplifiedMode : CandidateMode → Set
    suppressedMode : CandidateMode → Set

record EisensteinTuringAnalogyBoundary : Set₁ where
  constructor eisensteinTuringAnalogyBoundary
  field
    symmetrySummed : SymmetrySummedModeGeometry
    instabilitySelected : InstabilitySelectedModeGeometry

    turingLane : ModeGeometryLane
    eisensteinLane : ModeGeometryLane

    turingLaneAnchor : turingLane ≡ turingReactionDiffusionLane
    eisensteinLaneAnchor : eisensteinLane ≡ eisensteinSymmetrySummationLane

    sharedModeGeometryVocabulary : Set
    distinctGenerationMechanisms : Set
    noSeriesEqualsReactionDiffusionClaim : Set
    noArithmeticDeterminesPerceptClaim : Set
