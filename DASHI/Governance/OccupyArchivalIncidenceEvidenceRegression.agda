module DASHI.Governance.OccupyArchivalIncidenceEvidenceRegression where

open import DASHI.Core.Prelude
import DASHI.Governance.OccupyArchivalIncidenceEvidenceExact as Archive

archiveAvailabilityIsPaid :
  Archive.archiveAvailabilityPaid Archive.canonicalOccupyArchivalIncidenceBoundary ≡ true
archiveAvailabilityIsPaid = refl

pseudonymousTokensAreUsed :
  Archive.pseudonymousTokensUsed Archive.canonicalOccupyArchivalIncidenceBoundary ≡ true
pseudonymousTokensAreUsed = refl

rawNamesNotPropagated :
  Archive.rawNamesPropagatedIntoDerivedCandidates Archive.canonicalOccupyArchivalIncidenceBoundary ≡ false
rawNamesNotPropagated = refl

attendanceDoesNotCreateIssueIncidence :
  Archive.attendanceImpliesIssueParticipation Archive.canonicalOccupyArchivalIncidenceBoundary ≡ false
attendanceDoesNotCreateIssueIncidence = refl

agendaDoesNotCreateDecision :
  Archive.agendaMentionImpliesDecision Archive.canonicalOccupyArchivalIncidenceBoundary ≡ false
agendaDoesNotCreateDecision = refl

minutesAreNotAssumedComplete :
  Archive.minutesAssumedCompleteTranscript Archive.canonicalOccupyArchivalIncidenceBoundary ≡ false
minutesAreNotAssumedComplete = refl

workingGroupDoesNotGeneraliseToWholeOWS :
  Archive.workingGroupEvidenceGeneralisesToAllOWS Archive.canonicalOccupyArchivalIncidenceBoundary ≡ false
workingGroupDoesNotGeneraliseToAllOWS = refl

boundedSpeakerInteractionPaysCandidate :
  Archive.paysParticipationEdge Archive.boundedSpeakerProposalCandidate ≡ true
boundedSpeakerInteractionPaysCandidate = refl
