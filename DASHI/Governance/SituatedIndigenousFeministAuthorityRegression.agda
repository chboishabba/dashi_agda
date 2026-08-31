module DASHI.Governance.SituatedIndigenousFeministAuthorityRegression where

open import DASHI.Core.Prelude
import DASHI.Core.RecognitionConstitutionNonfactorabilityExact as Recognition
import DASHI.Core.SituatedClaimAuthoritySystemExact as Situated
import DASHI.Governance.IndigenousAuthorityEnvelopeExact as Envelope
import DASHI.Governance.FirstNationsOwnedEvidenceContractExact as FirstNations
import DASHI.Governance.SmithResearchAgendaAuthorityBoundaryExact as Smith
import DASHI.Governance.MoretonRobinsonRecognitionSovereigntyBoundaryExact as Moreton
import DASHI.Governance.WhyteKinshipTemporalityBoundaryExact as Whyte
import DASHI.Governance.FeministRecognitionAuthorityCrossPollinationExact as Feminist

------------------------------------------------------------------------
-- Focused regression receipt for the three coupled spines:
-- material/empirical, epistemic-authority, political/sovereignty.
------------------------------------------------------------------------

recognitionFactorizationBlocked :
  Recognition.FactorsThroughRecognition Recognition.demoSystem → ⊥
recognitionFactorizationBlocked = Recognition.recognitionDoesNotRecoverAuthority

studyIsNotIntervention :
  Situated.DemoPermission Situated.community Situated.claim Situated.researchConsumer Situated.interventionUse → ⊥
studyIsNotIntervention = Situated.studyPermissionDoesNotBecomeInterventionPermission

externalDescriptionNotSovereignty :
  Envelope.AuthorityEnvelope.sovereignStanding Envelope.externalPublishedDescription ≡
  Envelope.originatingAuthority → ⊥
externalDescriptionNotSovereignty = Envelope.externalDescriptionIsNotOriginatingAuthority

ownedProvenanceNotNormativeByItself :
  FirstNations.AuthorizedFor FirstNations.firstNationsOwned FirstNations.normativeAuthority → ⊥
ownedProvenanceNotNormativeByItself =
  FirstNations.ownedProvenanceAloneDoesNotAuthorizeNormativeAuthority

smithCorrectnessNotAgendaClosure :
  Smith.agendaStatus Smith.communityAgenda ≡ Smith.agendaStatus Smith.externalAgenda → ⊥
smithCorrectnessNotAgendaClosure = Smith.differentAgendaAuthority

settlerRecognitionNotSovereigntyExhaustion :
  Recognition.FactorsThroughRecognition Moreton.recognitionSystem → ⊥
settlerRecognitionNotSovereigntyExhaustion =
  Moreton.settlerRecognitionCannotExhaustSovereignAuthority

presentBurdenNotRelationalHistory :
  (recover : Whyte.PresentBurdenCode → Whyte.RelationalJusticeCode) →
  ((x : Whyte.RelationalHistory) →
    recover (Whyte.presentBurdenObserver x) ≡ Whyte.relationalHistoryObserver x) → ⊥
presentBurdenNotRelationalHistory = Whyte.presentBurdenDoesNotRecoverRelationalHistory

feministVisibleSurfaceNotSituatedExhaustion :
  Recognition.FactorsThroughRecognition Feminist.commonSystem → ⊥
feministVisibleSurfaceNotSituatedExhaustion =
  Feminist.visibleSurfaceDoesNotExhaustSituatedCoordinate

record SituatedAuthorityCapstoneBoundary : Set where
  constructor situatedAuthorityCapstoneBoundary
  field
    symbolicLegibilityEqualsOntologicalExhaustion : Bool
    symbolicLegibilityEqualsOntologicalExhaustionIsFalse :
      symbolicLegibilityEqualsOntologicalExhaustion ≡ false
    empiricalAdequacyEqualsEpistemicAuthorization : Bool
    empiricalAdequacyEqualsEpistemicAuthorizationIsFalse :
      empiricalAdequacyEqualsEpistemicAuthorization ≡ false
    epistemicAuthorizationEqualsPoliticalSovereignty : Bool
    epistemicAuthorizationEqualsPoliticalSovereigntyIsFalse :
      epistemicAuthorizationEqualsPoliticalSovereignty ≡ false
    politicalCritiqueImpliesEmpiricalInvalidity : Bool
    politicalCritiqueImpliesEmpiricalInvalidityIsFalse :
      politicalCritiqueImpliesEmpiricalInvalidity ≡ false

canonicalSituatedAuthorityCapstoneBoundary : SituatedAuthorityCapstoneBoundary
canonicalSituatedAuthorityCapstoneBoundary =
  situatedAuthorityCapstoneBoundary false refl false refl false refl false refl
