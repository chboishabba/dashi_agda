module DASHI.Interop.SensibLawSnowballAttributionLineageAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Cognition.PNF.SensibLawSourceRealisedLegalRuleExact as SourceRule
import DASHI.Cognition.PNF.SensibLawLegalClaimProvenanceLineageExact as Lineage

------------------------------------------------------------------------
-- SENSIBLAW SOURCE RECEIPT -> SNOWBALL SOURCE ROLE + CLAIM LINEAGE
--
-- The canonical snowball attribution owner retains source identity/role/
-- visibility and the proof/authority firewalls. SensibLaw adds an independent
-- legal-claim provenance stage. This adapter therefore projects a legal source
-- receipt to the generic source-role invariant while retaining, rather than
-- collapsing, the legal-claim stage.
------------------------------------------------------------------------

propositionSourceSnowballReceipt :
  ∀ {p} (receipt : SourceRule.PropositionSourceReceipt p) →
  Snowball.SourceRoleSnowballReceipt (SourceRule.attributedSource receipt)
propositionSourceSnowballReceipt receipt =
  Snowball.canonicalSourceRoleSnowballReceipt
    (SourceRule.attributedSource receipt)

propositionSourceExternalLineage :
  ∀ {p} (receipt : SourceRule.PropositionSourceReceipt p) →
  Lineage.ClaimLineageReceipt p
propositionSourceExternalLineage = Lineage.externalClaimFromSourceReceipt

propositionSourceReconstructionLineage :
  ∀ {p} (receipt : SourceRule.PropositionSourceReceipt p) →
  String →
  Lineage.ClaimLineageReceipt p
propositionSourceReconstructionLineage =
  Lineage.reconstructionFromSourceReceipt

sameSourceReceiptDoesNotFixClaimStage :
  ∀ {p} (receipt : SourceRule.PropositionSourceReceipt p) (reference : String) →
  Lineage.stageOf (propositionSourceExternalLineage receipt) ≡
  Lineage.stageOf (propositionSourceReconstructionLineage receipt reference) →
  ⊥
sameSourceReceiptDoesNotFixClaimStage receipt reference ()

record SensibLawSnowballLineageBoundary : Set where
  constructor sensiblaw-snowball-lineage-boundary
  field
    legalSourceReceiptProjectsToSnowballSourceRole : Bool
    legalClaimStageRetainedSeparately : Bool
    sameSourceIdentityDeterminesClaimStage : Bool
    citationCreatesLegalAuthority : Bool
    repositoryReconstructionBecomesExternalSourceClaim : Bool

canonicalSensibLawSnowballLineageBoundary : SensibLawSnowballLineageBoundary
canonicalSensibLawSnowballLineageBoundary =
  sensiblaw-snowball-lineage-boundary
    true
    true
    false
    false
    false
