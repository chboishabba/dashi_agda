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
import DASHI.Culture.WitchSelfIdentificationPredicateUseBidiExact as WitchUse
import DASHI.Culture.WitchRelationalAttributionDialogueBidiExact as Rel

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

sameWitchTokenDifferentUse : Symbol.token Symbol.imposedWitchEpisode ≡ Symbol.token Symbol.reclaimedWitchEpisode
sameWitchTokenDifferentUse = Symbol.sameTokenAcrossEpisodes

sameWordDoesNotRecoverUse : Symbol.SymbolicInversionAuthorityTransferBoundary.sameWordMeansSameHistoricalUse Symbol.canonicalSymbolicInversionAuthorityTransferBoundary ≡ false
sameWordDoesNotRecoverUse = refl

reclamationPreservesOriginalProvenance : Symbol.ReclamationErasesOriginalProvenance → ⊥
reclamationPreservesOriginalProvenance = Symbol.reclamationDoesNotEraseOriginalProvenance

witchSentenceLiteralPinned : WitchUse.naturalLanguage WitchUse.canonicalWitchSelfIdentification ≡ "I am a witch."
witchSentenceLiteralPinned = refl

sameWitchSentenceCannotRecoverUse : WitchUse.WitchSelfIdentificationBoundary.sameSentenceDeterminesSameUse WitchUse.canonicalWitchSelfIdentificationBoundary ≡ false
sameWitchSentenceCannotRecoverUse = refl

witchDoesNotDefaultToWiccan : WitchUse.WitchSentencePromotesWiccanAffiliation → ⊥
witchDoesNotDefaultToWiccan = WitchUse.witchSentenceDoesNotPromoteWiccanAffiliation

witchDoesNotDefaultToFeminist : WitchUse.WitchSentencePromotesFeministPolitics → ⊥
witchDoesNotDefaultToFeminist = WitchUse.witchSentenceDoesNotPromoteFeministPolitics

presentWitchIdentityDoesNotRecoverChildhoodRoute : WitchUse.PresentIdentityPromotesChildhoodFormationRoute → ⊥
presentWitchIdentityDoesNotRecoverChildhoodRoute = WitchUse.presentIdentityDoesNotPromoteChildhoodFormationRoute

wittgensteinStillNotFabricated : WitchUse.WitchSelfIdentificationBoundary.unrecoveredWittgensteinSourceIsNotCited WitchUse.canonicalWitchSelfIdentificationBoundary ≡ true
wittgensteinStillNotFabricated = refl

------------------------------------------------------------------------
-- Relational attribution / dialogue regression.
------------------------------------------------------------------------

selfSurfacePinned : Rel.surface Rel.selfWitch ≡ "I am a witch."
selfSurfacePinned = refl

externalSurfacePinned : Rel.surface Rel.youWitch ≡ "You are a witch."
externalSurfacePinned = refl

historicalSurfacePinned : Rel.surface Rel.historicalWitch ≡ "She was a witch."
historicalSurfacePinned = refl

samePredicateNotSameRelationalAct : Rel.WitchRelationalAttributionBoundary.samePredicateMeansSameRelationalAct Rel.canonicalWitchRelationalAttributionBoundary ≡ false
samePredicateNotSameRelationalAct = refl

externalLabelNotTargetAssent : Rel.ExternalAttributionPromotesTargetAssent → ⊥
externalLabelNotTargetAssent = Rel.externalAttributionDoesNotPromoteTargetAssent

accusationNotHistoricalFact : Rel.AccusationPromotesHistoricalFact → ⊥
accusationNotHistoricalFact = Rel.accusationDoesNotPromoteHistoricalFact

historicalClassificationNotHistoricalSelfIdentification : Rel.HistoricalRecordPromotesSelfIdentification → ⊥
historicalClassificationNotHistoricalSelfIdentification = Rel.historicalRecordDoesNotPromoteSelfIdentification

quotationNotEndorsement : Rel.QuotationPromotesSpeakerEndorsement → ⊥
quotationNotEndorsement = Rel.quotationDoesNotPromoteSpeakerEndorsement

reclaimedQuotationNotOriginalMeaning : Rel.ReclaimedQuotationPromotesOriginalMeaning → ⊥
reclaimedQuotationNotOriginalMeaning = Rel.reclaimedQuotationDoesNotPromoteOriginalMeaning

hostileLabelNotPrivateIdentity : Rel.HostileLabelPromotesPrivateIdentity → ⊥
hostileLabelNotPrivateIdentity = Rel.hostileLabelDoesNotPromotePrivateIdentity

responseDoesNotEraseInitialProvenance : Rel.WitchRelationalAttributionBoundary.targetResponseErasesInitialProvenance Rel.canonicalWitchRelationalAttributionBoundary ≡ false
responseDoesNotEraseInitialProvenance = refl

relationalCoordinatesRequired : Rel.WitchRelationalAttributionBoundary.relationalModeRequiresIndependentCoordinates Rel.canonicalWitchRelationalAttributionBoundary ≡ true
relationalCoordinatesRequired = refl
