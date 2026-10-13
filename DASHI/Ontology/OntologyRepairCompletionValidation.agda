module DASHI.Ontology.OntologyRepairCompletionValidation where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.WikidataRepairProposal as Repair
open import DASHI.Ontology.OntologyRepairCompletionExact

llmOnlyEvidenceCannotAuthorizeDestructiveRepair :
  DestructiveRepairAuthority llmOnlyEvidence → ⊥
llmOnlyEvidenceCannotAuthorizeDestructiveRepair = llmOnlyNotDestructive

pluralReviewedEvidenceMayRouteRedundantSuperclass :
  routedOperation redundantSuperclassFinding pluralReviewedEvidence
  ≡ Repair.removeRedundantSuperclass
pluralReviewedEvidenceMayRouteRedundantSuperclass = refl

versionChangeReopensReviewedCase :
  nextLifecycle reviewedState sourceChanged ≡ reopenedState
versionChangeReopensReviewedCase = refl

realFixturePinsWikidataTarget :
  realLgbtDBFilmFestivalObjectId ≡ "Q220505"
realFixturePinsWikidataTarget = refl

realFixtureDoesNotAssertTruth :
  ExternalFixtureTruthPermission → ⊥
realFixtureDoesNotAssertTruth = externalFixtureCannotAssertTruth

climateAmbiguityAbstains :
  climateDisposition ambiguousStatementBundle ≡ abstainMigration
climateAmbiguityAbstains = refl

aliasResolutionDoesNotEqualConceptGap :
  TitleResolutionTruthPermission aliasResolvedExisting → ⊥
aliasResolutionDoesNotEqualConceptGap = titleResolutionCannotAssertConceptTruth

endToEndProposalRemainsReviewOnly :
  Repair.RepairProposalTruthPermission Repair.proposalForReviewOnly → ⊥
endToEndProposalRemainsReviewOnly = Repair.repairProposalCannotAssertOntologyTruth

canonicalCompletionReceipt :
  endToEndCaseOwned canonicalCompletionStatus ≡ true
canonicalCompletionReceipt = endToEndCaseOwnedIsTrue canonicalCompletionStatus
