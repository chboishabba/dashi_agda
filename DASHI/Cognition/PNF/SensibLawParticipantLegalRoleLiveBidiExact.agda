module DASHI.Cognition.PNF.SensibLawParticipantLegalRoleLiveBidiExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawSemanticStatusProductExact as Status
import DASHI.Cognition.PNF.SensibLawClaimAtomOntologyVerticalSliceExact as Vertical
import DASHI.Cognition.PNF.SensibLawParticipantLegalRoleWrongTypeBidiExact as LegalRole

------------------------------------------------------------------------
-- LIVE PARTICIPANT -> LEGAL ROLE REGRESSION
--
-- The same actor/event is interpreted under two different WrongType/system
-- fibres.  The linguistic role remains Agent in both.  Any DutyBearer or other
-- legal role is supplied only by an explicit legal-role resolver receipt.
------------------------------------------------------------------------

dogActor : Ontology.Actor
dogActor =
  Ontology.actor
    (Ontology.stableId "actor:X")
    "X"
    (Ontology.stableId "actor-class:person")

dogSemanticSubject : Status.SemanticSubject
dogSemanticSubject =
  Status.semanticSubject
    "actor:X"
    Status.entityReferent
    Status.agent
    Status.legalParticipantUnresolved
    Status.identityResolvedSame
    Status.antecedentResolved

fixtureSystem : Ontology.StableId
fixtureSystem = Ontology.stableId "legal-system:fixture"

alternateSystem : Ontology.StableId
alternateSystem = Ontology.stableId "legal-system:alternate"

fixtureWrongType : Ontology.WrongType
fixtureWrongType =
  Ontology.wrongTypeRecord
    (Ontology.stableId "wrong:fixture:dog-duty")
    fixtureSystem
    [] [] [] []
    Ontology.negligent
    [] [] []

alternateWrongType : Ontology.WrongType
alternateWrongType =
  Ontology.wrongTypeRecord
    (Ontology.stableId "wrong:alternate:dog-duty")
    alternateSystem
    [] [] [] []
    Ontology.strict
    [] [] []

fixtureInterpretation : Ontology.WrongTypeInterpretation
fixtureInterpretation =
  Ontology.interpretation
    (Ontology.Event.eventId Vertical.dogEvent)
    (Ontology.WrongType.wrongTypeId fixtureWrongType)
    fixtureSystem
    (Ontology.Perspective.perspectiveId Vertical.dogPerspective)
    Ontology.suggested
    []
    "fixture same-event WrongType interpretation"

alternateInterpretation : Ontology.WrongTypeInterpretation
alternateInterpretation =
  Ontology.interpretation
    (Ontology.Event.eventId Vertical.dogEvent)
    (Ontology.WrongType.wrongTypeId alternateWrongType)
    alternateSystem
    (Ontology.Perspective.perspectiveId Vertical.dogPerspective)
    Ontology.contested
    []
    "alternate-system same-event WrongType interpretation"

fixtureDutyBearerWeld : LegalRole.ParticipantLegalRoleWeld
fixtureDutyBearerWeld =
  LegalRole.participantLegalRoleWeld
    dogSemanticSubject
    dogActor
    Vertical.dogEvent
    fixtureWrongType
    fixtureInterpretation
    Status.dutyBearer
    refl refl refl refl
    ("same actor/event evidence" ∷ "fixture WrongType source" ∷ [])
    "explicit fixture legal-role resolver"
    "legal role projection policy"

alternateRightsBearerWeld : LegalRole.ParticipantLegalRoleWeld
alternateRightsBearerWeld =
  LegalRole.participantLegalRoleWeld
    dogSemanticSubject
    dogActor
    Vertical.dogEvent
    alternateWrongType
    alternateInterpretation
    Status.rightsBearer
    refl refl refl refl
    ("same actor/event evidence" ∷ "alternate-system WrongType source" ∷ [])
    "explicit alternate legal-role resolver"
    "alternate legal role projection policy"

linguisticRoleSurvivesFixtureProjection :
  LegalRole.legalRoleProjectionKeepsLinguisticRole fixtureDutyBearerWeld
  ≡ Status.agent
linguisticRoleSurvivesFixtureProjection = refl

linguisticRoleSurvivesAlternateProjection :
  LegalRole.legalRoleProjectionKeepsLinguisticRole alternateRightsBearerWeld
  ≡ Status.agent
linguisticRoleSurvivesAlternateProjection = refl

sameEventCrossSystemComparison : LegalRole.CrossSystemParticipantComparison
sameEventCrossSystemComparison =
  LegalRole.crossSystemParticipantComparison
    fixtureDutyBearerWeld
    alternateRightsBearerWeld
    refl
    fixtureSystem
    alternateSystem
    refl
    refl

------------------------------------------------------------------------
-- Explicit resolution is necessary; this fixture does not make Agent itself
-- a legal-role constructor.
------------------------------------------------------------------------

data FixtureDutyBearerMakesAllAgentsDutyBearers : Set where

data CrossSystemRoleDifferenceIsContradiction : Set where

fixtureDoesNotGeneraliseAgentToDutyBearer :
  FixtureDutyBearerMakesAllAgentsDutyBearers → ⊥
fixtureDoesNotGeneraliseAgentToDutyBearer ()

crossSystemDifferenceIsNotContradiction :
  CrossSystemRoleDifferenceIsContradiction → ⊥
crossSystemDifferenceIsNotContradiction ()
