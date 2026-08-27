module DASHI.Biology.SolisProjectProvenanceExact where

------------------------------------------------------------------------
-- SOLIS / SCN PROJECT PROVENANCE
--
-- This owner corrects and sharpens the provenance boundary for the Solis
-- material used in the neurodivergent/social-ecology tranche.
--
-- Supplied archive evidence identifies the conceptual source being discussed as
-- Instagram handle `@solishood`.  The local project archive is reported at:
--
--   chboishabba/dashiTRADE
--   ignore.TRADER_CANTEXT.md:61211--62174
--
-- with the SCN/integrity material around the supplied line anchors, including
-- the 1/2 threshold, `AutisticSignal[x] := Check[SystemicIntegrity[x]]`, and
-- collapse-risk/qPARA language.
--
-- Historical DASHI commit
--   2f45a6da102cf582503281ace8c508031f17fdbb
-- contains related cognition substrate (integrity/synchrony, network diffusion,
-- ternary decision and residual/safety machinery) but no standalone Solis/SCN
-- module and no exact autism-specific integrity functional.
--
-- The handle attribution is project/archive provenance supplied in the current
-- reconstruction.  It is not independently verified here as a scholarly
-- identity, peer-reviewed mechanism source, or empirical autism authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record SolisProjectProvenance : Set where
  constructor solis-project-provenance
  field
    conceptualHandle : String
    archiveRepository : String
    archiveLocator : String
    historicalSubstrateCommit : String
    historicalIntegrityOwner : String
    historicalNetworkOwner : String
    handleAttributionFromSuppliedArchive : Bool
    handleIdentityIndependentlyVerifiedHere : Bool
    peerReviewedSolisMechanismAuthority : Bool
    standaloneHistoricalSCNModuleLocated : Bool
    exactAutismIntegrityFunctionalHistoricallyLocated : Bool

open SolisProjectProvenance public

canonicalSolisProjectProvenance : SolisProjectProvenance
canonicalSolisProjectProvenance =
  solis-project-provenance
    "@solishood (Instagram; identified in supplied project notes)"
    "chboishabba/dashiTRADE"
    "ignore.TRADER_CANTEXT.md:61211-62174; supplied anchors include ~61294 threshold, ~61341 AutisticSignal checker, ~62174 qPARA/collapse handling"
    "2f45a6da102cf582503281ace8c508031f17fdbb"
    "DASHI/Cognition/NetworkIntegritySynchronyMetrics.agda"
    "DASHI/Cognition/PsychedelicNetworkDiffusion.agda"
    true
    false
    false
    false
    false

------------------------------------------------------------------------
-- Distinguish conceptual-source provenance from later DASHI mathematics.
------------------------------------------------------------------------

data AttributionRole : Set where
  solisConceptualSource
  dashiHistoricalSubstrate
  dashiCurrentFormalExtension
  peerReviewedEmpiricalSource
  : AttributionRole

solisHandleRole : AttributionRole
solisHandleRole = solisConceptualSource

historicalDashiRole : AttributionRole
historicalDashiRole = dashiHistoricalSubstrate

currentSCNFormalisationRole : AttributionRole
currentSCNFormalisationRole = dashiCurrentFormalExtension

solisHandleRoleIsNotEmpiricalAuthority :
  solisHandleRole ≡ peerReviewedEmpiricalSource → ⊥
solisHandleRoleIsNotEmpiricalAuthority ()

historicalDashiRoleIsNotSolisConceptualAuthorship :
  historicalDashiRole ≡ solisConceptualSource → ⊥
historicalDashiRoleIsNotSolisConceptualAuthorship ()

currentFormalExtensionIsNotHistoricalSource :
  currentSCNFormalisationRole ≡ dashiHistoricalSubstrate → ⊥
currentFormalExtensionIsNotHistoricalSource ()

record SolisAttributionBoundary : Set where
  constructor solis-attribution-boundary
  field
    suppliedNotesIdentifySolishoodHandle : Bool
    suppliedNotesIdentifySolishoodHandleIsTrue :
      suppliedNotesIdentifySolishoodHandle ≡ true
    archiveAndHandleProvenanceAreScholarlyValidation : Bool
    archiveAndHandleProvenanceAreScholarlyValidationIsFalse :
      archiveAndHandleProvenanceAreScholarlyValidation ≡ false
    laterDashiResidualBranchingMathAttributedToSolishood : Bool
    laterDashiResidualBranchingMathAttributedToSolishoodIsFalse :
      laterDashiResidualBranchingMathAttributedToSolishood ≡ false
    historicalDashiSubstrateEqualsStandaloneSCN : Bool
    historicalDashiSubstrateEqualsStandaloneSCNIsFalse :
      historicalDashiSubstrateEqualsStandaloneSCN ≡ false

canonicalSolisAttributionBoundary : SolisAttributionBoundary
canonicalSolisAttributionBoundary =
  solis-attribution-boundary
    true refl
    false refl
    false refl
    false refl
