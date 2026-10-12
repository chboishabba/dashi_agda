module DASHI.Reasoning.GrokkingGeometricCrystallisationAttributionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ATTRIBUTION / AUTHORITY LEDGER FOR THE GROKKING-CRYSTALLISATION SYNTHESIS
--
-- This module exists so that later cross-pollination cannot silently collapse
-- external source claims, DASHIg empirical outputs, and DASHI synthesis into a
-- single authorship or evidentiary category.
------------------------------------------------------------------------

data ProvenanceClass : Set where
  externalScientificSource : ProvenanceClass
  externalEngineeringSource : ProvenanceClass
  dashigEmpiricalOutput : ProvenanceClass
  dashiFormalSynthesis : ProvenanceClass

data AuthorityClass : Set where
  sourceClaimAuthority : AuthorityClass
  boundedEmpiricalReceipt : AuthorityClass
  formalRepresentationReceipt : AuthorityClass
  hypothesisOnly : AuthorityClass

record AttributionReceipt : Set where
  constructor attribution-receipt
  field
    label : String
    provenanceClass : ProvenanceClass
    authorityClass : AuthorityClass
    crossPollinationTransfersAuthorship : Bool
    crossPollinationTransfersAuthorshipIsFalse :
      crossPollinationTransfersAuthorship ≡ false
    interpretation : String

open AttributionReceipt public

originalGrokkingLiteratureReceipt : AttributionReceipt
originalGrokkingLiteratureReceipt =
  attribution-receipt
    "Power et al. and subsequent grokking literature"
    externalScientificSource
    sourceClaimAuthority
    false refl
    "External literature remains source for the empirical grokking phenomenon and source-specific mechanistic observations. DASHI reuse does not transfer authorship."

lilaEngineeringReceipt : AttributionReceipt
lilaEngineeringReceipt =
  attribution-receipt
    "LILA / Leech-Lila implementation surfaces"
    externalEngineeringSource
    sourceClaimAuthority
    false refl
    "External implementations are engineering evidence under their own provenance; repository mirroring or import does not establish authorship."

dashigExperimentReceipt : AttributionReceipt
dashigExperimentReceipt =
  attribution-receipt
    "DASHIg preliminary geometry-vs-plain grokking experiment"
    dashigEmpiricalOutput
    boundedEmpiricalReceipt
    false refl
    "DASHIg owns the pinned experiment outputs/timings, not the upstream imported architecture; preliminary timing differences do not establish universal superiority."

dashCrystallisationSynthesisReceipt : AttributionReceipt
dashCrystallisationSynthesisReceipt =
  attribution-receipt
    "DASHI grokking ~= geometric crystallisation / routing refinement synthesis"
    dashiFormalSynthesis
    hypothesisOnly
    false refl
    "DASHI owns the cross-stack formal synthesis and non-promotion boundaries. Universal crystallisation, learned-router causality, FC-layer necessity, and biological identity remain empirical hypotheses."

record AttributionBoundary : Set where
  constructor attribution-boundary
  field
    importedImplementationImpliesAuthorship : Bool
    externalClaimImpliesIndependentReplication : Bool
    preliminaryTimingImpliesArchitectureSuperiority : Bool
    formalAnalogyImpliesMechanismIdentity : Bool
    traumaAnalogyCreatesClinicalAuthority : Bool
    e8FitCreatesHumanLanguageMechanism : Bool

open AttributionBoundary public

canonicalAttributionBoundary : AttributionBoundary
canonicalAttributionBoundary =
  attribution-boundary false false false false false false
