module DASHI.Core.FormalizationRecoveryGeometryExact where

------------------------------------------------------------------------
-- FORMALIZATION / HISTORICAL RECOVERY GEOMETRY
--
-- Generic owner for a distinction that matters both to autoformalization and
-- to historical reconstruction of formal calculi:
--
--   (1) translation / transcription into a formal presentation;
--   (2) reconstruction of omitted assumptions, context, intended structure,
--       or proof obligations.
--
-- These are orthogonal obligations.  A syntactically valid translation can be
-- semantically or historically inadequate, while a good reconstruction of the
-- intended context does not by itself provide a machine-checkable translation.
--
-- SOURCE / METHOD CALIBRATION
--
-- Andrea Asperti, Alberto Naibo, Claudio Sacerdoti Coen,
-- "Thinking Machines: Mathematical Reasoning in the Age of LLMs", 2026.
-- arXiv:2508.00459v2.
-- The supplied preprint explicitly separates translation difficulty from
-- mathematical reconstruction difficulty in autoformalization.  Its displayed
-- journal DOI is not treated here as a verified final publication identifier;
-- the arXiv identifier is the stable source handle used by this module.
--
-- Roy Wagner,
-- "Mathematical Abstraction as Unstable Translation Between Concrete
-- Presentations", Philosophy of Mathematics Education Journal 35, 2019.
-- ETH Research Collection permanent identifier:
-- DOI: 10.3929/ethz-b-000387100.
-- Wagner is calibration for treating translation between presentations as
-- partial / context-sensitive rather than assuming a universal invariant core.
--
-- The records and obstruction lemmas below are local DASHI formalizations; the
-- cited sources calibrate the distinction and terminology rather than serving
-- as proof certificates for the Agda theorems.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Two independent recovery obligations.
------------------------------------------------------------------------

record FormalizationRecoveryProblem : Set₁ where
  constructor formalizationRecoveryProblem
  field
    SourcePresentation : Set
    FormalPresentation : Set
    ReconstructedContext : Set

    translate : SourcePresentation → FormalPresentation
    reconstructContext : SourcePresentation → ReconstructedContext

    TranslationAdequate : SourcePresentation → Set
    ReconstructionAdequate : SourcePresentation → Set

open FormalizationRecoveryProblem public

FullyRecovered :
  (problem : FormalizationRecoveryProblem) →
  SourcePresentation problem → Set
FullyRecovered problem source =
  TranslationAdequate problem source ×
  ReconstructionAdequate problem source

fullRecoveryHasTranslation :
  (problem : FormalizationRecoveryProblem) →
  (source : SourcePresentation problem) →
  FullyRecovered problem source →
  TranslationAdequate problem source
fullRecoveryHasTranslation problem source recovered = proj₁ recovered

fullRecoveryHasReconstruction :
  (problem : FormalizationRecoveryProblem) →
  (source : SourcePresentation problem) →
  FullyRecovered problem source →
  ReconstructionAdequate problem source
fullRecoveryHasReconstruction problem source recovered = proj₂ recovered

------------------------------------------------------------------------
-- Explicit independence witnesses.
------------------------------------------------------------------------

record TranslationOnlyWitness
    (problem : FormalizationRecoveryProblem)
    (source : SourcePresentation problem) : Set₁ where
  constructor translationOnlyWitness
  field
    translationAdequate : TranslationAdequate problem source
    reconstructionFails : ReconstructionAdequate problem source → ⊥

open TranslationOnlyWitness public

record ReconstructionOnlyWitness
    (problem : FormalizationRecoveryProblem)
    (source : SourcePresentation problem) : Set₁ where
  constructor reconstructionOnlyWitness
  field
    reconstructionAdequate : ReconstructionAdequate problem source
    translationFails : TranslationAdequate problem source → ⊥

open ReconstructionOnlyWitness public

translationOnlyBlocksCollapse :
  (problem : FormalizationRecoveryProblem) →
  (source : SourcePresentation problem) →
  TranslationOnlyWitness problem source →
  (TranslationAdequate problem source →
   ReconstructionAdequate problem source) →
  ⊥
translationOnlyBlocksCollapse problem source witness collapse =
  reconstructionFails witness (collapse (translationAdequate witness))

reconstructionOnlyBlocksCollapse :
  (problem : FormalizationRecoveryProblem) →
  (source : SourcePresentation problem) →
  ReconstructionOnlyWitness problem source →
  (ReconstructionAdequate problem source →
   TranslationAdequate problem source) →
  ⊥
reconstructionOnlyBlocksCollapse problem source witness collapse =
  translationFails witness (collapse (reconstructionAdequate witness))

------------------------------------------------------------------------
-- Recovery stages are labels, not a theorem that later stages follow merely
-- from earlier ones.  They are useful for provenance-aware audit surfaces.
------------------------------------------------------------------------

data RecoveryStage : Set where
  sourceLocated : RecoveryStage
  primaryTextInspected : RecoveryStage
  transcriptionExtracted : RecoveryStage
  formalObjectReconstructed : RecoveryStage
  theoremObligationDischarged : RecoveryStage

record RecoveryStageProfile : Set₁ where
  constructor recoveryStageProfile
  field
    Supports : RecoveryStage → Set

open RecoveryStageProfile public

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record FormalizationRecoveryGeometryBoundary : Set where
  constructor formalizationRecoveryGeometryBoundary
  field
    translationAndReconstructionAreSeparateObligations : Bool
    translationAndReconstructionAreSeparateObligationsIsTrue :
      translationAndReconstructionAreSeparateObligations ≡ true

    sourceLocatedMeansFormalObjectRecovered : Bool
    sourceLocatedMeansFormalObjectRecoveredIsFalse :
      sourceLocatedMeansFormalObjectRecovered ≡ false

    syntacticTranslationMeansHistoricalSemanticAdequacy : Bool
    syntacticTranslationMeansHistoricalSemanticAdequacyIsFalse :
      syntacticTranslationMeansHistoricalSemanticAdequacy ≡ false

    recoveryStagesAreAutomaticImplicationChain : Bool
    recoveryStagesAreAutomaticImplicationChainIsFalse :
      recoveryStagesAreAutomaticImplicationChain ≡ false

canonicalFormalizationRecoveryGeometryBoundary :
  FormalizationRecoveryGeometryBoundary
canonicalFormalizationRecoveryGeometryBoundary =
  formalizationRecoveryGeometryBoundary
    true refl
    false refl
    false refl
    false refl
