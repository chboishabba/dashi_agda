module DASHI.Culture.AmyEskridgeOSINTChronologyCorroborationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.AmyEskridgeOSINTChronologySnowballExact as Chron
import DASHI.Culture.AmyEskridgeOSINTSnowballExact as OSINT

------------------------------------------------------------------------
-- AMY ESKRIDGE MEMORIAL: CHRONOLOGY CORROBORATION / CONTRADICTION
--
-- Corroboration is counted by independent origin, not outlet count. Repeated
-- articles downstream of the same Milburn/message lineage remain one origin.
-- Contradictions are retained as source-quality evidence and acquisition hints;
-- they do not themselves create a forensic or causal conclusion.
------------------------------------------------------------------------

data CorroborationDisposition : Set where
  independentlyCorroborated : CorroborationDisposition
  sameOriginRepeated : CorroborationDisposition
  singleOriginOnly : CorroborationDisposition
  contradictionDetected : CorroborationDisposition
  corroborationUnresolved : CorroborationDisposition

data ContradictionClass : Set where
  noContradiction : ContradictionClass
  biographicalMetadataConflict : ContradictionClass
  dateConflict : ContradictionClass
  propositionConflict : ContradictionClass
  sourceRoleConflict : ContradictionClass

record ChronologyCorroborationAtom : Set where
  constructor chronology-corroboration-atom
  field
    chronologyReference : String
    propositionReference : String
    originGroupReference : String
    corroboration : CorroborationDisposition
    contradiction : ContradictionClass
    comparisonReference : String
    independentOriginCountKnown : Bool
    exactNativeCarrierStillRequired : Bool
    createsCauseOfDeathFinding : Bool
    createsActorIdentityFinding : Bool

open ChronologyCorroborationAtom public

------------------------------------------------------------------------
-- Strongest currently corroborated public fact: date/age from family memorial.
------------------------------------------------------------------------

deathDateCorroboration : ChronologyCorroborationAtom
deathDateCorroboration = chronology-corroboration-atom
  "Chron.deathDateChronology"
  "Amy died 2022-06-11 aged 34"
  "family-obituary-origin"
  independentlyCorroborated
  noContradiction
  "AL.com and Legacy expose the same family-obituary carrier; this supports the narrow memorial proposition, not cause or manner"
  true false false false

------------------------------------------------------------------------
-- May-message reporting: multiple outlets, currently one attributable origin
-- lineage (Milburn / reported screenshots), so outlet multiplicity is not
-- independent corroboration.
------------------------------------------------------------------------

may13MessageCorroboration : ChronologyCorroborationAtom
may13MessageCorroboration = chronology-corroboration-atom
  "Chron.may13ReportedNonSuicideMessage"
  "reported May 13 non-suicide/overdose statement"
  "milburn-reported-message-origin"
  sameOriginRepeated
  noContradiction
  "Hindustan Times, later articles, and public-post references reproduce the same Milburn-attributed message lineage"
  true true false false

may19MessageCorroboration : ChronologyCorroborationAtom
may19MessageCorroboration = chronology-corroboration-atom
  "Chron.may19ReportedDirectedEnergyMessage"
  "reported May 19 burns / RF K-band statement"
  "milburn-reported-message-origin"
  sameOriginRepeated
  noContradiction
  "later articles repeat the May 19 claim but no independently originated native message or apparatus evidence is paid here"
  true true false false

intrusionCorroboration : ChronologyCorroborationAtom
intrusionCorroboration = chronology-corroboration-atom
  "Chron.intrusionStatementChronology"
  "Amy reported repeated apartment entries and property disturbance"
  "amy-first-person-interview-origin"
  singleOriginOnly
  noContradiction
  "archived Amy interview supports speaker attribution; independent apartment/security/police corroboration remains open"
  true false false false

------------------------------------------------------------------------
-- Source-quality contradiction: one downstream article calls Amy 24, whereas
-- the family obituary establishes age 34. This is evidence about reporting
-- reliability/provenance, not evidence for any death hypothesis.
------------------------------------------------------------------------

ageMetadataContradiction : ChronologyCorroborationAtom
ageMetadataContradiction = chronology-corroboration-atom
  "post-2026 secondary reporting"
  "age at death"
  "downstream-republication-origin"
  contradictionDetected
  biographicalMetadataConflict
  "IGV downstream article says 24; family obituary says 34"
  true false false false

------------------------------------------------------------------------
-- Broader federal inquiry is independently established by an official House
-- carrier, but that does not corroborate Amy-specific cause/link propositions.
------------------------------------------------------------------------

houseInquiryCorroboration : ChronologyCorroborationAtom
houseInquiryCorroboration = chronology-corroboration-atom
  "Chron.houseReviewChronology"
  "broader federal missing-scientists inquiry exists"
  "house-oversight-2026-missing-scientists-origin"
  independentlyCorroborated
  noContradiction
  "official House letters independently establish inquiry/request-for-briefing context; they do not establish an Amy-specific case connection"
  true false false false

record ChronologyCorroborationBoundary : Set where
  constructor chronology-corroboration-boundary
  field
    outletCountEqualsIndependentOriginCount : Bool
    sameOriginRepetitionUpgradesAuthentication : Bool
    metadataContradictionCreatesDeathTheory : Bool
    independentHouseInquiryCorroboratesAmySpecificCause : Bool
    singleOriginFirstPersonStatementEqualsEventCorroboration : Bool
    contradictorySecondaryMetadataMayLowerTrustInThatCarrier : Bool
    contradictionMayCreateNewAcquisitionTarget : Bool
    independentOriginsMustRemainDistinct : Bool

open ChronologyCorroborationBoundary public

canonicalChronologyCorroborationBoundary : ChronologyCorroborationBoundary
canonicalChronologyCorroborationBoundary = chronology-corroboration-boundary
  false false false false false true true true

-- Exact owner alignments retained.
deathDateChronologyStillExactPublicCarrier :
  Chron.carrierStrength Chron.deathDateChronology ≡ Chron.exactPublicCarrier
deathDateChronologyStillExactPublicCarrier = refl

may13StillSourceOfSource :
  Chron.carrierStrength Chron.may13ReportedNonSuicideMessage ≡ Chron.sourceOfSourceLead
may13StillSourceOfSource = refl

reportedMessageStillOSINTLead :
  OSINT.carrierRelation OSINT.reportedNonSuicideMessageLeadAtom ≡ OSINT.discoveryLeadOnly
reportedMessageStillOSINTLead = refl
