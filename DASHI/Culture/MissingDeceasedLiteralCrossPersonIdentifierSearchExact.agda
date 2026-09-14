module DASHI.Culture.MissingDeceasedLiteralCrossPersonIdentifierSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedCommonObjectProgrammeDiscriminatorExact as Common
import DASHI.Culture.AmyEskridgeMechanismAssociationProvenanceExact as AmyAssoc

------------------------------------------------------------------------
-- SECOND OBJECT-FIRST INVESTIGATION PASS
--
-- Search priority: literal identifiers and explicit person-to-person/source
-- relations before thematic similarity.  A literal reference is weaker than a
-- common programme receipt unless the same object/work package is paid.
------------------------------------------------------------------------

data CrossPersonRelationClass : Set where
  explicitPersonWorkReference
  sharedInstitutionOnly
  postEventGovernmentAggregation
  singlePersonProgrammeIdentifier
  allegedProfessionalLink
  literalCommonProgrammeIdentifier
  preEventOperationalIdentifier : CrossPersonRelationClass

record CrossPersonIdentifierSearchReceipt : Set where
  constructor cross-person-identifier-search-receipt
  field
    relationClass : CrossPersonRelationClass
    participantA : String
    participantB : String
    identifierOrObject : String
    sourceReference : String
    literalRelationPaid : Bool
    commonProgrammePaid : Bool
    preEventOperationalLinkPaid : Bool
    discriminator : String

open CrossPersonIdentifierSearchReceipt public

amyNamesNingHAL5 : CrossPersonIdentifierSearchReceipt
amyNamesNingHAL5 = cross-person-identifier-search-receipt
  explicitPersonWorkReference
  "Amy Eskridge"
  "Ning Li"
  "HAL5-Dec2018-Talk-AntiGravity.pdf / slide 'Ning Li & Doug Torr AC Gravity (1990s)'"
  "AmyEskridgeMechanismAssociationProvenanceExact.liTorrAssociation; HAL5-hosted 2018 deck"
  true false false
  "Amy explicitly discussed Ning Li/Torr/AC Gravity as historical antigravity research. This pays awareness/reference, not shared team, apparatus, contract, custody or operational action."

houseOversightPostEventAggregation : CrossPersonIdentifierSearchReceipt
houseOversightPostEventAggregation = cross-person-identifier-search-receipt
  postEventGovernmentAggregation
  "multiple retained U.S. scientist cases"
  "multiple retained U.S. scientist cases"
  "House Oversight missing-scientists inquiry / letters dated 2026-04-20; Committee staff contact dated 2026-04-16 in DoW letter"
  "U.S. House Committee on Oversight and Government Reform missing-scientists letters"
  true false false
  "This is a literal cross-case government aggregation after the events and public/media convergence. It does not pay a pre-event common programme or targeting operation."

ningArmyIdentifierSinglePersonOnly : CrossPersonIdentifierSearchReceipt
ningArmyIdentifierSinglePersonOnly = cross-person-identifier-search-receipt
  singlePersonProgrammeIdentifier
  "Ning Li / AC Gravity"
  "no second retained scientist yet welded"
  "DAAH01-01-9-R001 / Gravito-Electro Magnetic Superconductivity Experiment"
  "FY2001 DoD cooperative-agreement/other-transaction locator; primary row/SOW still acquisition debt"
  true false false
  "A strong programme identifier exists for Ning/AC Gravity, but no inspected receipt currently names a second retained scientist on that identifier."

jplHicksMaiwaldInstitutionOnly : CrossPersonIdentifierSearchReceipt
jplHicksMaiwaldInstitutionOnly = cross-person-identifier-search-receipt
  sharedInstitutionOnly
  "Michael David Hicks"
  "Frank W. Maiwald"
  "Jet Propulsion Laboratory / Caltech"
  "JPL/CNEOS Hicks science surfaces; JPL/SURP Maiwald spectroscopy surfaces"
  true false false
  "Same institution is real, but inspected surfaces expose distinct small-body photometry and molecular-spectroscopy objects."

nudtChenFengInstitutionOnly : CrossPersonIdentifierSearchReceipt
nudtChenFengInstitutionOnly = cross-person-identifier-search-receipt
  sharedInstitutionOnly
  "Chen Shuming"
  "Feng Yanghe"
  "National University of Defense Technology"
  "NUDT Galaxy/Feiteng history; NUDT Feng military-intelligence/decision research surfaces"
  true false false
  "Shared strategic institution does not identify one common task, contract, work package or apparatus."

nudtFengZhangInstitutionOnly : CrossPersonIdentifierSearchReceipt
nudtFengZhangInstitutionOnly = cross-person-identifier-search-receipt
  sharedInstitutionOnly
  "Feng Yanghe"
  "Zhang Daibing"
  "National University of Defense Technology"
  "NUDT Feng research surfaces; NUDT Zhang robotics/unmanned-systems history"
  true false false
  "Inspected NUDT sources currently pay institutional overlap but distinct technical objects."

rezaMcCaslandAllegationOnly : CrossPersonIdentifierSearchReceipt
rezaMcCaslandAllegationOnly = cross-person-identifier-search-receipt
  allegedProfessionalLink
  "Monica Jacinto / Monica Reza"
  "William Neil McCasland"
  "AFRL/Mondaloy alleged professional connection"
  "2026-04-20 House Oversight letter characterises the claimed direct link as unconfirmed public reporting; official AFRL chronology separately records McCasland leadership"
  true false false
  "Official repetition of an allegation is not a same-work-package receipt. Leadership over AFRL also does not retroactively create direct involvement in a specific materials programme."

currentIdentifierSearchReceipts : List CrossPersonIdentifierSearchReceipt
currentIdentifierSearchReceipts =
  amyNamesNingHAL5 ∷ houseOversightPostEventAggregation ∷
  ningArmyIdentifierSinglePersonOnly ∷ jplHicksMaiwaldInstitutionOnly ∷
  nudtChenFengInstitutionOnly ∷ nudtFengZhangInstitutionOnly ∷
  rezaMcCaslandAllegationOnly ∷ []

literalPersonReferenceCount : Nat
literalPersonReferenceCount = 1

postEventGovernmentAggregationCount : Nat
postEventGovernmentAggregationCount = 1

literalCommonProgrammeIdentifierCount : Nat
literalCommonProgrammeIdentifierCount = 0

preEventOperationalIdentifierCount : Nat
preEventOperationalIdentifierCount = 0

literalPersonReferencePaysCommonProgramme : Bool
literalPersonReferencePaysCommonProgramme = false

postEventGovernmentAggregationPaysPreEventLinkage : Bool
postEventGovernmentAggregationPaysPreEventLinkage = false

singlePersonProgrammeIdentifierPaysCrossPersonLink : Bool
singlePersonProgrammeIdentifierPaysCrossPersonLink = false

preMediaCrossCaseOperationalIdentifierPaid : Bool
preMediaCrossCaseOperationalIdentifierPaid = false

amyHistoricalReferencePaysNingProgrammeMembership : Bool
amyHistoricalReferencePaysNingProgrammeMembership = false

houseInquiryPaysPriorGovernmentKnowledge : Bool
houseInquiryPaysPriorGovernmentKnowledge = false

currentHypothesisPromotion : Common.HypothesisClass
currentHypothesisPromotion = Common.H1

h2PaidAfterLiteralIdentifierSearch : Bool
h2PaidAfterLiteralIdentifierSearch = false

h3PaidAfterLiteralIdentifierSearch : Bool
h3PaidAfterLiteralIdentifierSearch = false

nextIdentifierSearch : String
nextIdentifierSearch =
  "recover primary DAAH01-01-9-R001 row/SOW/closeout and search its personnel/subcontract/facility identifiers; search exact AFRL Mondaloy contract numbers and JPL/NUDT work-package identifiers; search for any cross-case security/tasking identifier dated before 2026-04 public aggregation"
