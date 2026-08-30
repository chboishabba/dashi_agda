module DASHI.JohnAnthonyBrownPaperBidiValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.DecisionAutonomyExact as Autonomy
import DASHI.Culture.JohnAnthonyBrownChildReligiousPowerBidiExact as Brown
import DASHI.Culture.JohnAnthonyBrownDocumentLineageExact as Lineage
import DASHI.Culture.JohnAnthonyBrownStudyDesignBidiExact as Design
import DASHI.Culture.JohnAnthonyBrownPaperSectionHypothesisManifestExact as Manifest
import DASHI.Culture.ChildReligiousAutonomyFormationBidiExact as Formation
import DASHI.Culture.ChildReligiousEpistemicReopeningBidiExact as Epistemic
import DASHI.Culture.ReligiousThreatPredicateDialecticBidiExact as Threat
import DASHI.Culture.ReligiousSanctionFeministWiccaCrossPollinationExact as FW
import DASHI.Culture.SymbolicInversionAuthorityTransferBidiExact as Symbol

------------------------------------------------------------------------
-- Focused consumer root for the paper-specific BIDI owners.
------------------------------------------------------------------------

authorAttributionPinned : Brown.BrownPaperSource.author Brown.johnAnthonyBrownPaper ≡ "John Anthony Brown"
authorAttributionPinned = Brown.johnAnthonyBrownIsAttributedAuthor

latestDocumentAuthorPinned : Lineage.BrownDocumentSnapshot.attributedAuthor Lineage.latestProposalSnapshot ≡ "John Anthony Brown"
latestDocumentAuthorPinned = Lineage.latestProposalAuthor

conditionalHypothesesPreserved : Brown.JohnAnthonyBrownPaperBidiBoundary.paperPositiveAndNegativeOutcomeHypothesesPreserved Brown.canonicalJohnAnthonyBrownPaperBidiBoundary ≡ true
conditionalHypothesesPreserved = refl

ordinaryTeachingNotEntrapment : Brown.JohnAnthonyBrownPaperBidiBoundary.ordinaryReligiousTeachingEqualsEntrapment Brown.canonicalJohnAnthonyBrownPaperBidiBoundary ≡ false
ordinaryTeachingNotEntrapment = refl

hellFearRemainsResearchableMechanism : Brown.JohnAnthonyBrownPaperBidiBoundary.hellFearMechanismMayBeResearchable Brown.canonicalJohnAnthonyBrownPaperBidiBoundary ≡ true
hellFearRemainsResearchableMechanism = refl

mechanismResemblanceNotLegalElements : Brown.MechanismResemblancePromotesLegalElements → ⊥
mechanismResemblanceNotLegalElements = Brown.mechanismResemblanceDoesNotPromoteLegalElements

sameParticipationSurfacePinned : Formation.publicSurface Formation.openFormationEpisode ≡ Formation.publicSurface Formation.closedFormationEpisode
sameParticipationSurfacePinned = refl

participationNotConsent : Formation.ParticipationPromotesConsent → ⊥
participationNotConsent = Formation.participationDoesNotPromoteConsent

fearNotEntrapment : Formation.FearPromotesEntrapment → ⊥
fearNotEntrapment = Formation.fearDoesNotPromoteEntrapment

professionNotAutonomousEndorsement : Epistemic.ProfessionPromotesAutonomousEndorsement → ⊥
professionNotAutonomousEndorsement = Epistemic.professionDoesNotPromoteAutonomousEndorsement

counterEvidenceNotSafeRevision : Epistemic.CounterEvidenceAccessPromotesSafeRevision → ⊥
counterEvidenceNotSafeRevision = Epistemic.counterEvidenceDoesNotPromoteSafeRevision

hellThreatLiteralPinned : Threat.naturalLanguage Threat.hellThreatAssertion ≡ "If you do X, you're going to hell."
hellThreatLiteralPinned = refl

bareThreatNotPressureCandidate : Threat.BareUtterancePromotesPressureCandidate → ⊥
bareThreatNotPressureCandidate = Threat.bareUtteranceDoesNotPromotePressureCandidate

pressureCandidateNotEntrapment : Threat.PressureCandidatePromotesEntrapment → ⊥
pressureCandidateNotEntrapment = Threat.pressureCandidateDoesNotPromoteEntrapment

behaviourEffectDoesNotProveThreatTruth : Threat.BehaviourEffectPromotesThreatTruth → ⊥
behaviourEffectDoesNotProveThreatTruth = Threat.behaviourEffectDoesNotPromoteThreatTruth

doctrinalCounterclaimNotNegation : Threat.doctrinalCounterclaim ≡ Threat.logicalNegation → ⊥
doctrinalCounterclaimNotNegation = Threat.doctrinalCounterclaimNotLogicalNegation

sanctionNotFeministIdentity : FW.ReligiousSanctionPromotesFeminism → ⊥
sanctionNotFeministIdentity = FW.religiousSanctionDoesNotPromoteFeminism

sanctionNotWiccanIdentity : FW.ReligiousSanctionPromotesWiccanIdentity → ⊥
sanctionNotWiccanIdentity = FW.religiousSanctionDoesNotPromoteWiccanIdentity

laterWiccanIdentityNotPriorCoercion : FW.LaterWiccanIdentityPromotesPriorCoercion → ⊥
laterWiccanIdentityNotPriorCoercion = FW.laterWiccanIdentityDoesNotPromotePriorCoercion

wiccanReclamationNotAncientLineage : FW.WiccanReclamationPromotesAncientLineage → ⊥
wiccanReclamationNotAncientLineage = FW.wiccanReclamationDoesNotPromoteAncientLineage

counterFormationNotGuaranteedSynthesis : FW.CounterFormationPromotesSynthesis → ⊥
counterFormationNotGuaranteedSynthesis = FW.counterFormationDoesNotPromoteSynthesis

------------------------------------------------------------------------
-- Symbolic inversion / authority-transfer regression.
------------------------------------------------------------------------

sameWitchTokenDifferentUse : Symbol.token Symbol.imposedWitchEpisode ≡ Symbol.token Symbol.reclaimedWitchEpisode
sameWitchTokenDifferentUse = Symbol.sameTokenAcrossEpisodes

sameWordDoesNotRecoverUse : Symbol.SymbolicInversionAuthorityTransferBoundary.sameWordMeansSameHistoricalUse Symbol.canonicalSymbolicInversionAuthorityTransferBoundary ≡ false
sameWordDoesNotRecoverUse = refl

reclamationDoesNotRewriteOriginalEvent : Symbol.SymbolicInversionAuthorityTransferBoundary.reclamationRewritesOriginalEvent Symbol.canonicalSymbolicInversionAuthorityTransferBoundary ≡ false
reclamationDoesNotRewriteOriginalEvent = refl

reclamationPreservesOriginalProvenance : Symbol.ReclamationErasesOriginalProvenance → ⊥
reclamationPreservesOriginalProvenance = Symbol.reclamationDoesNotEraseOriginalProvenance

institutionalAuthorityDoesNotEstablishTruth : Symbol.ImposedAuthorityTransfersTruth → ⊥
institutionalAuthorityDoesNotEstablishTruth = Symbol.imposedAuthorityDoesNotTransferTruth

sharedReclaimedSymbolNotSharedDoctrine : Symbol.SharedTokenPromotesSharedDoctrine → ⊥
sharedReclaimedSymbolNotSharedDoctrine = Symbol.sharedTokenDoesNotPromoteSharedDoctrine

sharedReclaimedSymbolNotSharedPolitics : Symbol.SharedTokenPromotesSharedPolitics → ⊥
sharedReclaimedSymbolNotSharedPolitics = Symbol.sharedTokenDoesNotPromoteSharedPolitics

sharedReclaimedSymbolNotSharedFormationHistory : Symbol.SharedTokenPromotesSharedFormationHistory → ⊥
sharedReclaimedSymbolNotSharedFormationHistory = Symbol.sharedTokenDoesNotPromoteSharedFormationHistory

symbolicPositiveRechartNeedsResidual : Symbol.SymbolicInversionAuthorityTransferBoundary.positiveRechartRequiresResidualBeyondWord Symbol.canonicalSymbolicInversionAuthorityTransferBoundary ≡ true
symbolicPositiveRechartNeedsResidual = refl

symbolicDialecticalRoleFrameRelative : Symbol.SymbolicInversionAuthorityTransferBoundary.dialecticalRoleIsFrameRelative Symbol.canonicalSymbolicInversionAuthorityTransferBoundary ≡ true
symbolicDialecticalRoleFrameRelative = refl
