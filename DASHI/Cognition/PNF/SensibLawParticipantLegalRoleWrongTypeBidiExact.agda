module DASHI.Cognition.PNF.SensibLawParticipantLegalRoleWrongTypeBidiExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Interop.SensibLawOntologyTopology as Ontology

------------------------------------------------------------------------
-- BIDI CAMPAIGN 5: generic participant frame -> legal participant role.
--
-- The existing WrongType ontology is the legal owner.  A legal-role projection
-- must weld the semantic subject to the same literal Actor/Event/WrongType/
-- LegalSystem interpretation.  Linguistic participant role is evidence, never
-- the legal role constructor by itself.
------------------------------------------------------------------------

record ParticipantLegalRoleWeld : Set where
  constructor participantLegalRoleWeld
  field
    subject : Status.SemanticSubject
    actor : Ontology.Actor
    event : Ontology.Event
    wrongType : Ontology.WrongType
    interpretation : Ontology.WrongTypeInterpretation
    resultingLegalRole : Status.LegalParticipantRole
    subjectIsSameActor :
      Status.subjectReference subject
      ≡ Ontology.StableId.value (Ontology.Actor.actorId actor)
    interpretationIsSameEvent :
      Ontology.WrongTypeInterpretation.interpretedEvent interpretation
      ≡ Ontology.Event.eventId event
    interpretationIsSameWrongType :
      Ontology.WrongTypeInterpretation.interpretedAs interpretation
      ≡ Ontology.WrongType.wrongTypeId wrongType
    interpretationUsesDefiningSystem :
      Ontology.WrongTypeInterpretation.underSystem interpretation
      ≡ Ontology.WrongType.definingSystem wrongType
    evidenceReferences : List String
    resolverReference : String
    policyReference : String

open ParticipantLegalRoleWeld public

legalRoleProjectionKeepsLinguisticRole :
  ParticipantLegalRoleWeld → Status.ParticipantRole
legalRoleProjectionKeepsLinguisticRole weld =
  Status.participantRole (subject weld)

legalRoleProjectionResult :
  ParticipantLegalRoleWeld → Status.LegalParticipantRole
legalRoleProjectionResult = resultingLegalRole

------------------------------------------------------------------------
-- Same-object system fibre: another WrongType/system interpretation of the
-- same Event is not definitionally the same legal projection.
------------------------------------------------------------------------

record CrossSystemParticipantComparison : Set where
  constructor crossSystemParticipantComparison
  field
    left right : ParticipantLegalRoleWeld
    sameEvent :
      Ontology.Event.eventId (event left) ≡ Ontology.Event.eventId (event right)
    leftSystem : Ontology.StableId
    rightSystem : Ontology.StableId
    leftSystemExact :
      leftSystem ≡ Ontology.WrongTypeInterpretation.underSystem (interpretation left)
    rightSystemExact :
      rightSystem ≡ Ontology.WrongTypeInterpretation.underSystem (interpretation right)

open CrossSystemParticipantComparison public

------------------------------------------------------------------------
-- Hard no-go laws.
------------------------------------------------------------------------

data AgentAutomaticallyDutyBearer : Set where
data PatientAutomaticallyRightsBearer : Set where
data SameActorMeansSameLegalRoleAcrossSystems : Set where
data WrongTypeSuggestionIsConfirmedLiability : Set where
data LegalRoleProjectionChangesLinguisticRole : Set where

agentDoesNotAutoBecomeDutyBearer : AgentAutomaticallyDutyBearer → ⊥
agentDoesNotAutoBecomeDutyBearer ()

patientDoesNotAutoBecomeRightsBearer : PatientAutomaticallyRightsBearer → ⊥
patientDoesNotAutoBecomeRightsBearer ()

sameActorDoesNotCollapseSystems : SameActorMeansSameLegalRoleAcrossSystems → ⊥
sameActorDoesNotCollapseSystems ()

wrongTypeSuggestionDoesNotProveLiability : WrongTypeSuggestionIsConfirmedLiability → ⊥
wrongTypeSuggestionDoesNotProveLiability ()

legalProjectionDoesNotRewriteLinguisticRole : LegalRoleProjectionChangesLinguisticRole → ⊥
legalProjectionDoesNotRewriteLinguisticRole ()
