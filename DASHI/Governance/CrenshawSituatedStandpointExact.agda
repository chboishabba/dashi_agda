module DASHI.Governance.CrenshawSituatedStandpointExact where

-- DASHI-original finite standpoint / representation-role model.
-- Kimberle Crenshaw is attributed as a Black feminist legal scholar and
-- critic of antidiscrimination doctrine. The cited cases do NOT establish
-- that she served as counsel for their plaintiffs.
-- A hypothetical Black woman lawyer representing a client is a different
-- situated role, and neither role is a proxy for every Black woman's views.
-- Courtroom racial composition must be independently sourced; institutional
-- norms must not be inferred solely from the race of individual judges.

open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as INF

data ProfessionalRole : Set where
  legalScholar trialCounsel litigant judicialOfficer communityAdvocate :
    ProfessionalRole

data RelationToClaim : Set where
  interpretsDoctrine representsClient presentsOwnClaim
  adjudicatesClaim mobilisesCollectively : RelationToClaim

-- This finite example does not describe particular people or court records.
data SituatedProfessional : Set where
  scholarPosition counselPosition : SituatedProfessional

reportedProfession : SituatedProfessional → Bool
reportedProfession scholarPosition = true
reportedProfession counselPosition = true

professionalRole : SituatedProfessional → ProfessionalRole
professionalRole scholarPosition = legalScholar
professionalRole counselPosition = trialCounsel

professionalRelation : SituatedProfessional → RelationToClaim
professionalRelation scholarPosition = interpretsDoctrine
professionalRelation counselPosition = representsClient

professionLabelCannotRecoverProfessionalRole :
  INF.NonFactorabilityWitness reportedProfession professionalRole
professionLabelCannotRecoverProfessionalRole =
  INF.nonFactorabilityWitness scholarPosition counselPosition refl (λ ())

professionLabelCannotRecoverRepresentativeRelationship :
  INF.NonFactorabilityWitness reportedProfession professionalRelation
professionLabelCannotRecoverRepresentativeRelationship =
  INF.nonFactorabilityWitness scholarPosition counselPosition refl (λ ())

professionalLabelCannotEstablishCounselRole :
  INF.FactorsThrough reportedProfession professionalRole → ⊥
professionalLabelCannotEstablishCounselRole =
  INF.witnessRulesOutEveryFlatFactorisation
    professionLabelCannotRecoverProfessionalRole

-- A client's situated experience, counsel's professional duties, and an
-- academic critic's interpretations are separately admitted observations.
-- Co-reference of a legal controversy does not imply identity of authority.
data InstitutionalRole : Set where
  plaintiffRole counselRole scholarRole courtRole : InstitutionalRole

data ClaimAuthority : Set where
  livedAccount legalRepresentation scholarlyInterpretation
  judicialDisposition : ClaimAuthority

authorityOfRole : InstitutionalRole → ClaimAuthority
authorityOfRole plaintiffRole = livedAccount
authorityOfRole counselRole = legalRepresentation
authorityOfRole scholarRole = scholarlyInterpretation
authorityOfRole courtRole = judicialDisposition

scholarlyInterpretationIsNotClientRepresentation :
  authorityOfRole scholarRole ≡ authorityOfRole counselRole → ⊥
scholarlyInterpretationIsNotClientRepresentation ()

clientExperienceIsNotJudicialDisposition :
  authorityOfRole plaintiffRole ≡ authorityOfRole courtRole → ⊥
clientExperienceIsNotJudicialDisposition ()

-- Race/gender labels, inherited legal norms, and institutional power are
-- DISTINCT coordinates. These flags are possible observations, not diagnoses.
data CourtroomSituation : Set where
  sameRosterEqualVoice sameRosterSilencedVoice : CourtroomSituation

reportedPeople : CourtroomSituation → Bool
reportedPeople sameRosterEqualVoice = true
reportedPeople sameRosterSilencedVoice = true

effectiveVoice : CourtroomSituation → Bool
effectiveVoice sameRosterEqualVoice = true
effectiveVoice sameRosterSilencedVoice = false

courtRosterCannotRecoverVoice :
  INF.NonFactorabilityWitness reportedPeople effectiveVoice
courtRosterCannotRecoverVoice =
  INF.nonFactorabilityWitness
    sameRosterEqualVoice sameRosterSilencedVoice refl (λ ())

courtRosterNotSufficientToInferAuthority :
  INF.FactorsThrough reportedPeople effectiveVoice → ⊥
courtRosterNotSufficientToInferAuthority =
  INF.witnessRulesOutEveryFlatFactorisation
    courtRosterCannotRecoverVoice

-- For actual courts, independently source: venue, adjudicator, procedural
-- jurisdiction, voice/standing, claimant, advocate, and enforcement.
record StandpointEvidenceRequirements (Person Case : Set) : Set₁ where
  field
    personToCase : Person → Case → Set
    professionalAppointment : Person → Case → Set
    representedClientAuthority : Person → Case → Set
    situatedParticipation : Person → Case → Set
    institutionAndRules : Case → Set

-- No standalone source-world constructors inhabit the predicates above.
