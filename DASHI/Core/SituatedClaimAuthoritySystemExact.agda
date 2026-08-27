module DASHI.Core.SituatedClaimAuthoritySystemExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- SITUATED CLAIM AUTHORITY
--
-- Generic separation of empirical adequacy, research-agenda authority,
-- category authority, provenance, protocol, permission, contestability and
-- decision authority.  No implication between these coordinates is supplied
-- by default.
------------------------------------------------------------------------

record SituatedClaimAuthoritySystem : Set₁ where
  constructor situatedClaimAuthoritySystem
  field
    WorldState ResearchAgenda CategoryScheme Measurement Representation : Set
    Claim Community Consumer Use Obligation : Set

    agendaAuthorized : Community → ResearchAgenda → Set
    categoryAuthorized : Community → CategoryScheme → Set
    provenance : Claim → Community → Set
    protocolAllows : Community → Claim → Use → Set
    permission : Community → Claim → Consumer → Use → Set
    empiricallyAdequate : Claim → Consumer → Set
    politicallyContestable : Claim → Set
    decisionAuthorized : Community → Claim → Use → Set
    obligationSatisfied : Claim → Consumer → Use → Obligation → Set

record QualifiedUse
  (system : SituatedClaimAuthoritySystem)
  (claim : SituatedClaimAuthoritySystem.Claim system)
  (community : SituatedClaimAuthoritySystem.Community system)
  (consumer : SituatedClaimAuthoritySystem.Consumer system)
  (use : SituatedClaimAuthoritySystem.Use system)
  (obligation : SituatedClaimAuthoritySystem.Obligation system) : Set where
  constructor qualifiedUse
  field
    empiricalReceipt :
      SituatedClaimAuthoritySystem.empiricallyAdequate system claim consumer
    provenanceReceipt :
      SituatedClaimAuthoritySystem.provenance system claim community
    protocolReceipt :
      SituatedClaimAuthoritySystem.protocolAllows system community claim use
    permissionReceipt :
      SituatedClaimAuthoritySystem.permission system community claim consumer use
    obligationReceipt :
      SituatedClaimAuthoritySystem.obligationSatisfied system claim consumer use obligation

------------------------------------------------------------------------
-- Permission and intervention are intentionally different typed uses.
------------------------------------------------------------------------

data DemoUse : Set where
  studyUse interventionUse : DemoUse

data DemoCommunity : Set where community : DemoCommunity
data DemoClaim : Set where claim : DemoClaim
data DemoConsumer : Set where researchConsumer : DemoConsumer
data DemoAgenda : Set where agenda : DemoAgenda
data DemoCategory : Set where category : DemoCategory
data DemoWorld : Set where world : DemoWorld
data DemoMeasurement : Set where measurement : DemoMeasurement
data DemoRepresentation : Set where representation : DemoRepresentation
data DemoObligation : Set where attributionObligation : DemoObligation

data DemoAgendaAuthorized : DemoCommunity → DemoAgenda → Set where
  agendaReceipt : DemoAgendaAuthorized community agenda

data DemoCategoryAuthorized : DemoCommunity → DemoCategory → Set where
  categoryReceipt : DemoCategoryAuthorized community category

data DemoProvenance : DemoClaim → DemoCommunity → Set where
  provenanceReceipt : DemoProvenance claim community

data DemoProtocol : DemoCommunity → DemoClaim → DemoUse → Set where
  studyProtocol : DemoProtocol community claim studyUse

data DemoPermission : DemoCommunity → DemoClaim → DemoConsumer → DemoUse → Set where
  studyPermission : DemoPermission community claim researchConsumer studyUse

data DemoAdequacy : DemoClaim → DemoConsumer → Set where
  descriptiveAdequacy : DemoAdequacy claim researchConsumer

data DemoContestable : DemoClaim → Set where
  contestableClaim : DemoContestable claim

data DemoDecision : DemoCommunity → DemoClaim → DemoUse → Set where

data DemoObligationSatisfied : DemoClaim → DemoConsumer → DemoUse → DemoObligation → Set where
  attributionSatisfied :
    DemoObligationSatisfied claim researchConsumer studyUse attributionObligation

demoSystem : SituatedClaimAuthoritySystem
demoSystem = situatedClaimAuthoritySystem
  DemoWorld DemoAgenda DemoCategory DemoMeasurement DemoRepresentation
  DemoClaim DemoCommunity DemoConsumer DemoUse DemoObligation
  DemoAgendaAuthorized DemoCategoryAuthorized DemoProvenance DemoProtocol
  DemoPermission DemoAdequacy DemoContestable DemoDecision DemoObligationSatisfied

studyQualified :
  QualifiedUse demoSystem claim community researchConsumer studyUse attributionObligation
studyQualified = qualifiedUse descriptiveAdequacy provenanceReceipt studyProtocol studyPermission attributionSatisfied

studyPermissionDoesNotBecomeInterventionPermission :
  DemoPermission community claim researchConsumer interventionUse → ⊥
studyPermissionDoesNotBecomeInterventionPermission ()

studyPermissionDoesNotBecomeDecisionAuthority :
  DemoDecision community claim interventionUse → ⊥
studyPermissionDoesNotBecomeDecisionAuthority ()

record SituatedClaimAuthorityBoundary : Set where
  constructor situatedClaimAuthorityBoundary
  field
    empiricalAdequacyImpliesPermission : Bool
    empiricalAdequacyImpliesPermissionIsFalse : empiricalAdequacyImpliesPermission ≡ false
    correctAttributionImpliesArbitraryReuse : Bool
    correctAttributionImpliesArbitraryReuseIsFalse : correctAttributionImpliesArbitraryReuse ≡ false
    permissionToStudyImpliesConsentToIntervene : Bool
    permissionToStudyImpliesConsentToInterveneIsFalse :
      permissionToStudyImpliesConsentToIntervene ≡ false
    qualifiedUseTransfersSovereignty : Bool
    qualifiedUseTransfersSovereigntyIsFalse : qualifiedUseTransfersSovereignty ≡ false

canonicalSituatedClaimAuthorityBoundary : SituatedClaimAuthorityBoundary
canonicalSituatedClaimAuthorityBoundary =
  situatedClaimAuthorityBoundary false refl false refl false refl false refl
