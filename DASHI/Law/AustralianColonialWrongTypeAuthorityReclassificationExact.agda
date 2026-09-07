module DASHI.Law.AustralianColonialWrongTypeAuthorityReclassificationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Cognition.PNF.SensibLawWrongTypeApplicabilityLiabilityRemedyBidiExact as Wrong
import DASHI.Cognition.PNF.SensibLawParticipantLegalRoleWrongTypeBidiExact as Role
import DASHI.Law.AustralianColonialSemanticConstitutionSourceReceiptsExact as Source

------------------------------------------------------------------------
-- WrongType x colonial semantic constitution.
--
-- SensibLaw WrongType is an abstract wrong ontology, not a programming type
-- error.  This owner therefore keeps two layers separate:
--   (1) an analytical WrongType for authority-reclassifying colonial harm;
--   (2) the cross-order projection defect that maps antecedent law/authority
--       into a colonial administrative land/population category.
-- It does NOT declare a presently recognised cause of action or liability.
------------------------------------------------------------------------

colonialAnalyticalSystemId : Ontology.StableId
colonialAnalyticalSystemId = Ontology.stableId "DASHI.ANALYTICAL.COLONIAL-AUTHORITY"

cooperSourceId : Ontology.StableId
cooperSourceId = Ontology.stableId "source:Cooper-v-Stuart-1889-UKPC-16"

maboSourceId : Ontology.StableId
maboSourceId = Ontology.stableId "source:Mabo-v-Queensland-No2-1992-HCA-23"

uluruSourceId : Ontology.StableId
uluruSourceId = Ontology.stableId "source:Uluru-Statement-2017"

communityAuthorityInterestId : Ontology.StableId
communityAuthorityInterestId = Ontology.stableId "interest:community-authority"

countryTerritoryInterestId : Ontology.StableId
countryTerritoryInterestId = Ontology.stableId "interest:country-territory"

nonDominationInterestId : Ontology.StableId
nonDominationInterestId = Ontology.stableId "interest:non-domination"

colonialAuthorityReclassificationWrongType : Ontology.WrongType
colonialAuthorityReclassificationWrongType = Ontology.wrongTypeRecord
  (Ontology.stableId "wrong:dashi:colonial-authority-reclassification")
  colonialAnalyticalSystemId
  (cooperSourceId ∷ maboSourceId ∷ uluruSourceId ∷ [])
  (communityAuthorityInterestId ∷ countryTerritoryInterestId ∷ nonDominationInterestId ∷ [])
  [] [] Ontology.mixed [] [] []

------------------------------------------------------------------------
-- Projection defect: an antecedent normative order is not the same type of
-- object as a colonial land/population administration category.
------------------------------------------------------------------------

data AntecedentAuthorityType : Set where
  sovereignNormativeOrder
  communityPoliticalAuthority
  countryLawRelation : AntecedentAuthorityType

data ColonialAdministrativeType : Set where
  settledTerritory
  crownLandAdministration
  protectedPopulation
  assimilablePopulation : ColonialAdministrativeType

data ReclassificationEffect : Set where
  receptionOfEnglishLaw
  crownLandAvailability
  administrativeControl
  assimilationControl : ReclassificationEffect

record AuthorityReclassification : Set where
  constructor authorityReclassification
  field
    sourceType : AntecedentAuthorityType
    targetType : ColonialAdministrativeType
    operationalEffect : ReclassificationEffect
    sourceReference : String
    targetDoctrineReference : String
    sameNormativeType : Bool
    sameNormativeTypeIsFalse : sameNormativeType ≡ false
    sourceAuthorityPreservedByTarget : Bool

open AuthorityReclassification public

cooperSettledColonyReclassification : AuthorityReclassification
cooperSettledColonyReclassification = authorityReclassification
  sovereignNormativeOrder settledTerritory receptionOfEnglishLaw
  "First Nations antecedent law/authority as independently modelled source order"
  "Cooper v Stuart [1889] UKPC 16: NSW classified as practically unoccupied, without settled inhabitants or settled law"
  false refl false

maboRecognitionCorrection : AuthorityReclassification
maboRecognitionCorrection = authorityReclassification
  countryLawRelation crownLandAdministration crownLandAvailability
  "Mabo v Queensland (No 2) [1992] HCA 23: pre-existing rights under traditional laws/customs"
  "common-law recognition operates within Crown municipal law and does not convert Country into a Crown-created source"
  false refl true

------------------------------------------------------------------------
-- WrongType interpretation remains fibred by system and perspective.
------------------------------------------------------------------------

colonialProjectionEvent : Ontology.Event
colonialProjectionEvent = Ontology.event
  (Ontology.stableId "event:colonial-authority-reclassification")
  (Ontology.stableId "event-class:jurisdictional-reclassification")
  "1788-1992 analytical historical interval"
  "colonial legal-administrative reclassification of antecedent Country/law/authority"

analyticalPerspectiveId : Ontology.StableId
analyticalPerspectiveId = Ontology.stableId "perspective:dashi-source-bounded-colonial-audit"

colonialWrongTypeInterpretation : Ontology.WrongTypeInterpretation
colonialWrongTypeInterpretation = Ontology.interpretation
  (Ontology.Event.eventId colonialProjectionEvent)
  (Ontology.WrongType.wrongTypeId colonialAuthorityReclassificationWrongType)
  colonialAnalyticalSystemId
  analyticalPerspectiveId
  Ontology.suggested
  (cooperSourceId ∷ maboSourceId ∷ uluruSourceId ∷ [])
  "DASHI analytical classification over primary judicial and First Nations source receipts; not a court finding of present liability"

------------------------------------------------------------------------
-- BIDI routing: WrongType interpretation never skips applicability/elements.
------------------------------------------------------------------------

data ColonialWrongTypeClaim : Set where
  colonialAuthorityReclassificationIsCandidateWrongType
  colonialAuthorityReclassificationIsApplicableLegalWrong
  colonialWrongTypeWasViolated
  colonialWrongTypeCreatesPresentLiability
  colonialProjectionErasedAntecedentAuthority : ColonialWrongTypeClaim

data ColonialWrongTypeProducer : Set where
  analyticalWrongTypeInterpretationProducer
  applicabilityAndJurisdictionProducer
  proofRelevantElementProducer
  liabilityAndRemedyProducer
  beforeAfterAuthorityProjectionProducer : ColonialWrongTypeProducer

reverseColonialWrongType : ColonialWrongTypeClaim → ColonialWrongTypeProducer
reverseColonialWrongType colonialAuthorityReclassificationIsCandidateWrongType = analyticalWrongTypeInterpretationProducer
reverseColonialWrongType colonialAuthorityReclassificationIsApplicableLegalWrong = applicabilityAndJurisdictionProducer
reverseColonialWrongType colonialWrongTypeWasViolated = proofRelevantElementProducer
reverseColonialWrongType colonialWrongTypeCreatesPresentLiability = liabilityAndRemedyProducer
reverseColonialWrongType colonialProjectionErasedAntecedentAuthority = beforeAfterAuthorityProjectionProducer

wrongTypeInterpretationStillDoesNotAutoApply : Wrong.WrongTypeInterpretationAutomaticallyApplicable → ⊥
wrongTypeInterpretationStillDoesNotAutoApply = Wrong.wrongTypeInterpretationDoesNotAutoApply

sameActorStillDoesNotCollapseSystems : Role.SameActorMeansSameLegalRoleAcrossSystems → ⊥
sameActorStillDoesNotCollapseSystems = Role.sameActorDoesNotCollapseSystems

record ColonialWrongTypeBoundary : Set where
  constructor colonialWrongTypeBoundary
  field
    analyticalWrongTypeIsRecognisedCauseOfAction : Bool
    analyticalWrongTypeIsRecognisedCauseOfActionIsFalse : analyticalWrongTypeIsRecognisedCauseOfAction ≡ false
    analyticalWrongTypeProvesPresentLiability : Bool
    analyticalWrongTypeProvesPresentLiabilityIsFalse : analyticalWrongTypeProvesPresentLiability ≡ false
    colonialAdministrativeTargetSameTypeAsAntecedentAuthority : Bool
    colonialAdministrativeTargetSameTypeAsAntecedentAuthorityIsFalse : colonialAdministrativeTargetSameTypeAsAntecedentAuthority ≡ false
    maboRecognitionCreatesCountryAuthority : Bool
    maboRecognitionCreatesCountryAuthorityIsFalse : maboRecognitionCreatesCountryAuthority ≡ false
    neverCededPositionBecomesMunicipalHolding : Bool
    neverCededPositionBecomesMunicipalHoldingIsFalse : neverCededPositionBecomesMunicipalHolding ≡ false

canonicalColonialWrongTypeBoundary : ColonialWrongTypeBoundary
canonicalColonialWrongTypeBoundary =
  colonialWrongTypeBoundary false refl false refl false refl false refl false refl

sourceSynthesisRole : Source.ColonialSourceRole
sourceSynthesisRole = Source.dashiAnalyticalSynthesis
