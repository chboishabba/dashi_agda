module DASHI.Governance.WarOnDrugsHistoricalGenealogyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- WAR ON DRUGS HISTORICAL GENEALOGY
--
-- This module separates predecessor prohibition architecture, Nixon-era launch,
-- treatment/public-health actors, internal dissent, retrospective motive claims,
-- and later punitive escalation.  "Who started the War on Drugs?" therefore
-- becomes a role- and time-indexed question rather than a one-name answer.
------------------------------------------------------------------------

data DrugPolicyEra : Set where
  federalProhibitionPrehistory
  nixonLaunchEra
  nixonTreatmentExpansionEra
  nixonInternalDissentEra
  reaganPunitiveEscalationEra
  : DrugPolicyEra

data HistoricalActor : Set where
  harryAnslinger
  richardNixon
  johnMitchell
  johnEhrlichman
  egilKrogh
  jeromeJaffe
  raymondShafer
  ronaldReagan
  nancyReagan
  namedActor : String → HistoricalActor

data ActorRole : Set where
  predecessorEnforcementArchitect
  presidentialLaunchAuthority
  justiceEnforcementAuthority
  domesticPolicyCoordinator
  narcoticsPolicyProjectManager
  treatmentPublicHealthArchitect
  scientificPolicyDissent
  punitiveEscalationAuthority
  publicPreventionMobilizer
  : ActorRole

record ActorRoleReceipt : Set where
  constructor actorRoleReceipt
  field
    actor : HistoricalActor
    era : DrugPolicyEra
    role : ActorRole
    sourceReference : String
    roleScopeReference : String
    completeCausalAuthorship : Bool
    completeCausalAuthorshipIsFalse : completeCausalAuthorship ≡ false

open ActorRoleReceipt public

anslingerReceipt : ActorRoleReceipt
anslingerReceipt = actorRoleReceipt
  harryAnslinger
  federalProhibitionPrehistory
  predecessorEnforcementArchitect
  "DEA Museum: Anslinger served as first Federal Bureau of Narcotics commissioner from 1930 and helped craft domestic/international drug policy"
  "prehistory of federal prohibition/enforcement; not the 1971 presidential War-on-Drugs declaration"
  false refl

nixonReceipt : ActorRoleReceipt
nixonReceipt = actorRoleReceipt
  richardNixon
  nixonLaunchEra
  presidentialLaunchAuthority
  "17 June 1971 Nixon remarks: drug abuse described as public enemy number one and an all-out offensive announced"
  "formal modern presidential launch plus later 1973 DEA consolidation"
  false refl

mitchellReceipt : ActorRoleReceipt
mitchellReceipt = actorRoleReceipt
  johnMitchell
  nixonLaunchEra
  justiceEnforcementAuthority
  "Nixon-era Attorney General; participant in White House drug-policy planning and federal enforcement architecture"
  "Justice/enforcement role; not sole author of the policy regime"
  false refl

ehrlichmanReceipt : ActorRoleReceipt
ehrlichmanReceipt = actorRoleReceipt
  johnEhrlichman
  nixonLaunchEra
  domesticPolicyCoordinator
  "Nixon Domestic Council executive director; principal correspondent in Special Action Office drug-abuse records"
  "domestic-policy coordination and White House political context"
  false refl

kroghReceipt : ActorRoleReceipt
kroghReceipt = actorRoleReceipt
  egilKrogh
  nixonLaunchEra
  narcoticsPolicyProjectManager
  "Nixon Library finding aid: Krogh had narcotics/law-enforcement policy-making responsibility and managed a drug-policy staff"
  "substantial implementation/design role including development of coordinated federal response"
  false refl

jaffeReceipt : ActorRoleReceipt
jaffeReceipt = actorRoleReceipt
  jeromeJaffe
  nixonTreatmentExpansionEra
  treatmentPublicHealthArchitect
  "Jerome Jaffe led the Special Action Office for Drug Abuse Prevention and expanded treatment, methadone, rehabilitation, research and education"
  "internal public-health/treatment branch inside the Nixon regime"
  false refl

shaferReceipt : ActorRoleReceipt
shaferReceipt = actorRoleReceipt
  raymondShafer
  nixonInternalDissentEra
  scientificPolicyDissent
  "National Commission on Marihuana and Drug Abuse recommended against criminalizing private possession/use"
  "internal evidential/policy dissent from punitive marijuana treatment"
  false refl

reaganReceipt : ActorRoleReceipt
reaganReceipt = actorRoleReceipt
  ronaldReagan
  reaganPunitiveEscalationEra
  punitiveEscalationAuthority
  "Reagan-era federal escalation culminating in Anti-Drug Abuse Act 1986 and mandatory-minimum framework"
  "later escalation, not origin of the 1971 launch"
  false refl

nancyReceipt : ActorRoleReceipt
nancyReceipt = actorRoleReceipt
  nancyReagan
  reaganPunitiveEscalationEra
  publicPreventionMobilizer
  "Nancy Reagan became principal public spokesperson for the Just Say No prevention movement"
  "public prevention/moral-mobilization role; distinct from legislative authorship"
  false refl

canonicalActorGenealogy : List ActorRoleReceipt
canonicalActorGenealogy =
  anslingerReceipt ∷ nixonReceipt ∷ mitchellReceipt ∷ ehrlichmanReceipt ∷
  kroghReceipt ∷ jaffeReceipt ∷ shaferReceipt ∷ reaganReceipt ∷
  nancyReceipt ∷ []

------------------------------------------------------------------------
-- Retrospective motive evidence remains separately graded.
------------------------------------------------------------------------

data MotiveEvidenceGrade : Set where
  contemporaneousPrimary
  archivalAdministrative
  retrospectiveInterview
  contestedRetrospectiveInterview
  scholarlySynthesis
  : MotiveEvidenceGrade

record MotiveClaimReceipt : Set where
  constructor motiveClaimReceipt
  field
    actor : HistoricalActor
    grade : MotiveEvidenceGrade
    claimReference : String
    sourceReference : String
    contemporaneouslyCorroborated : Bool
    completeMotiveEstablished : Bool
    completeMotiveEstablishedIsFalse : completeMotiveEstablished ≡ false

open MotiveClaimReceipt public

ehrlichmanRetrospectiveClaim : MotiveClaimReceipt
ehrlichmanRetrospectiveClaim = motiveClaimReceipt
  johnEhrlichman
  contestedRetrospectiveInterview
  "1994 retrospective claim later published by Dan Baum: antiwar-left/hippie and Black-community disruption described as political use of marijuana/heroin criminalization"
  "Dan Baum, Harper's, 2016; quotation is historically important but retrospective and disputed by some Nixon associates/family"
  false
  false refl

------------------------------------------------------------------------
-- Counterculture is a political/social formation, not merely a drug category.
------------------------------------------------------------------------

data CountercultureFormation : Set where
  hippieCounterculture
  antiwarMovement
  blackPoliticalMovements
  youthRevolt
  veteranHeroinCrisis
  : CountercultureFormation

data CountercultureCoordinate : Set where
  drugPracticeCoordinate
  antiwarPoliticsCoordinate
  racializedPolicingCoordinate
  youthCultureCoordinate
  communalExperimentCoordinate
  musicArtSpiritualityCoordinate
  institutionalOppositionCoordinate
  : CountercultureCoordinate

record CountercultureSurface : Set where
  constructor countercultureSurface
  field
    formation : CountercultureFormation
    coordinates : List CountercultureCoordinate
    sourceReference : String
    reducedToDrugUse : Bool
    reducedToDrugUseIsFalse : reducedToDrugUse ≡ false

open CountercultureSurface public

hippieSurface : CountercultureSurface
hippieSurface = countercultureSurface
  hippieCounterculture
  (drugPracticeCoordinate ∷ youthCultureCoordinate ∷ communalExperimentCoordinate ∷
   musicArtSpiritualityCoordinate ∷ institutionalOppositionCoordinate ∷ [])
  "1960s counterculture literature: hippies as alternative social/cultural formation; marijuana and psychedelics were important but not exhaustive coordinates"
  false refl

antiwarSurface : CountercultureSurface
antiwarSurface = countercultureSurface
  antiwarMovement
  (antiwarPoliticsCoordinate ∷ youthCultureCoordinate ∷ institutionalOppositionCoordinate ∷ [])
  "antiwar movement retained separately from drug practice despite historical overlap with counterculture"
  false refl

------------------------------------------------------------------------
-- Hard historical boundaries.
------------------------------------------------------------------------

data AnslingerPromotesNixonWarAuthorship : Set where

data NixonLaunchPromotesUniformPunitivePolicy : Set where

data EhrlichmanQuotePromotesCompleteMotive : Set where

data HippieDrugAssociationPromotesCountercultureIdentity : Set where

data JaffeTreatmentPromotesNonPunitiveNixonRegime : Set where

anslingerDoesNotPromoteNixonAuthorship : AnslingerPromotesNixonWarAuthorship → ⊥
anslingerDoesNotPromoteNixonAuthorship ()

nixonLaunchDoesNotPromoteUniformPunitivePolicy : NixonLaunchPromotesUniformPunitivePolicy → ⊥
nixonLaunchDoesNotPromoteUniformPunitivePolicy ()

ehrlichmanQuoteDoesNotPromoteCompleteMotive : EhrlichmanQuotePromotesCompleteMotive → ⊥
ehrlichmanQuoteDoesNotPromoteCompleteMotive ()

hippieDrugAssociationDoesNotPromoteIdentity :
  HippieDrugAssociationPromotesCountercultureIdentity → ⊥
hippieDrugAssociationDoesNotPromoteIdentity ()

jaffeTreatmentDoesNotPromoteNonPunitiveRegime :
  JaffeTreatmentPromotesNonPunitiveNixonRegime → ⊥
jaffeTreatmentDoesNotPromoteNonPunitiveNixonRegime ()

record WarOnDrugsHistoricalGenealogyBoundary : Set where
  constructor warOnDrugsHistoricalGenealogyBoundary
  field
    modernWarOnDrugsHasPrehistory : Bool
    modernWarOnDrugsHasPrehistoryIsTrue : modernWarOnDrugsHasPrehistory ≡ true
    nixonProvidesFormalModernLaunch : Bool
    nixonProvidesFormalModernLaunchIsTrue : nixonProvidesFormalModernLaunch ≡ true
    nixonEraContainsPunitiveAndTreatmentBranches : Bool
    nixonEraContainsPunitiveAndTreatmentBranchesIsTrue :
      nixonEraContainsPunitiveAndTreatmentBranches ≡ true
    countercultureEqualsDrugUse : Bool
    countercultureEqualsDrugUseIsFalse : countercultureEqualsDrugUse ≡ false
    retrospectiveMotiveQuoteEqualsCompleteHistoricalCause : Bool
    retrospectiveMotiveQuoteEqualsCompleteHistoricalCauseIsFalse :
      retrospectiveMotiveQuoteEqualsCompleteHistoricalCause ≡ false

canonicalWarOnDrugsHistoricalGenealogyBoundary :
  WarOnDrugsHistoricalGenealogyBoundary
canonicalWarOnDrugsHistoricalGenealogyBoundary =
  warOnDrugsHistoricalGenealogyBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
