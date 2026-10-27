module DASHI.Ontology.OntologyRepairEndToEndValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.WikidataRepairProposal as Repair
import DASHI.Core.QueryFactorisationSufficiency as Factor
import DASHI.Ontology.OntologyRepairPluralityMaxCutExact as Plural
open import DASHI.Ontology.OntologyRepairEndToEndExact

caseUsesRealPinnedFixture :
  fixtureObjectId canonicalEndToEndCase ≡ "Q220505"
caseUsesRealPinnedFixture = refl

caseProposalRoutesToReview :
  Repair.operation (proposal canonicalEndToEndCase) ≡ Repair.holdForReview
caseProposalRoutesToReview = refl

mappingContributionKeepsOrigin :
  Plural.origin mappingEvidence ≡ Plural.mappingOrigin
mappingContributionKeepsOrigin = refl

llmContributionKeepsOrigin :
  Plural.origin llmEvidence ≡ Plural.llmOrigin
llmContributionKeepsOrigin = refl

humanContributionKeepsOrigin :
  Plural.origin humanEvidence ≡ Plural.humanReviewOrigin
humanContributionKeepsOrigin = refl

caseSubclassConsumerFactors :
  Factor.FactorsThrough questions projection query
caseSubclassConsumerFactors = factorisationReceipt canonicalEndToEndCase

sameProjectionCannotAnswerDisjointness :
  Factor.FactorsThrough questions projection disjointnessQuery → ⊥
sameProjectionCannotAnswerDisjointness = disjointnessNonFactorisation
