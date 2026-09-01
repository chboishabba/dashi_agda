module DASHI.Cognition.PNF.SensibLawSemanticStatusProductValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawSemanticStatusCrossPollinationExact as Cross
import DASHI.Cognition.PNF.SensibLawSpacyCompositionOnlySemanticConstitutionExact as Constitution

semanticRoleDoesNotCloseIdentity : Status.SemanticRoleDeterminesIdentity → ⊥
semanticRoleDoesNotCloseIdentity = Status.semanticRoleDoesNotDetermineIdentity

mentionDoesNotCloseOccurrence : Status.MentionDeterminesOccurrence → ⊥
mentionDoesNotCloseOccurrence = Status.mentionDoesNotDetermineOccurrence

assertionDoesNotCloseTruth : Status.AssertionDeterminesTruth → ⊥
assertionDoesNotCloseTruth = Status.assertionDoesNotDetermineTruth

holdingDoesNotCloseUniversalTruth : Status.CourtHoldingDeterminesUniversalTruth → ⊥
holdingDoesNotCloseUniversalTruth = Status.courtHoldingDoesNotDetermineUniversalTruth

agentDoesNotCloseDutyBearer : Status.LinguisticAgentDeterminesDutyBearer → ⊥
agentDoesNotCloseDutyBearer = Status.linguisticAgentDoesNotDetermineDutyBearer

applicabilityDoesNotCloseViolation : Status.ApplicabilityDeterminesViolation → ⊥
applicabilityDoesNotCloseViolation = Status.applicabilityDoesNotDetermineViolation

violationDoesNotCloseLiability : Status.ViolationDeterminesLiability → ⊥
violationDoesNotCloseLiability = Status.violationDoesNotDetermineLiability

reportingDoesNotCloseEmbeddedTruth : Cross.ReportingVerbMakesEmbeddedPropositionTrue → ⊥
reportingDoesNotCloseEmbeddedTruth = Cross.reportingDoesNotMakeEmbeddedTruth

legalAuthorityDoesNotClosePromotionAuthority : Cross.LegalAuthorityIsPromotionAuthority → ⊥
legalAuthorityDoesNotClosePromotionAuthority = Cross.legalAuthorityDoesNotEqualPromotionAuthority

oldExtractorCannotPromote :
  Cross.oldObligationExtractorMayPromoteStatus Cross.canonicalCrossPollinationBoundary ≡ false
oldExtractorCannotPromote = refl

legalIRDoesNotRediscover :
  Cross.legalIRMayRediscoverSemanticsIndependently Cross.canonicalCrossPollinationBoundary ≡ false
legalIRDoesNotRediscover = refl

candidateMayRemainUnresolved :
  Cross.candidateStatusMayRemainUnresolved Cross.canonicalCrossPollinationBoundary ≡ true
candidateMayRemainUnresolved = refl

regexStillForbidden : Constitution.RegexDerivedSemanticEvidence → ⊥
regexStillForbidden = Constitution.regexCannotBeSemanticEvidence
