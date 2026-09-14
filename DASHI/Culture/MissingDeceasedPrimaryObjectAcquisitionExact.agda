module DASHI.Culture.MissingDeceasedPrimaryObjectAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- PRIMARY-OBJECT ACQUISITION LEDGER
--
-- This layer records the best literal object/programme artefacts currently
-- located.  It separates a known primary locator from primary-byte custody,
-- and separates object existence from cross-person same-programme identity.
------------------------------------------------------------------------

data AcquisitionStatus : Set where
  primaryBytesInCustody
  primaryPublicObjectLocated
  primaryLocatorKnownBytesUninspected
  secondaryTranscriptionOnly
  institutionalPrimaryOnly
  searchResidual : AcquisitionStatus

record ObjectAcquisitionReceipt : Set where
  constructor object-acquisition-receipt
  field
    objectName : String
    identifier : String
    sourceClass : String
    status : AcquisitionStatus
    sourceReference : String
    personOrCarrier : String
    literalObjectPaid : Bool
    secondRetainedPersonPaid : Bool
    preEventOperationalLinkPaid : Bool
    whatRemains : String

open ObjectAcquisitionReceipt public

ningArmyOriginalRow : ObjectAcquisitionReceipt
ningArmyOriginalRow = object-acquisition-receipt
  "Gravito-Electro Magnetic Superconductivity Experiment"
  "DAAH01-01-9-R001"
  "FY2001 DoD Other Transactions report locator; archived official .doc known, bytes not independently inspected in this session"
  primaryLocatorKnownBytesUninspected
  "archived acq.osd.mil/dpap/Docs/FY01RPT.doc locator; matching secondary transcriptions"
  "Ning Li / AC Gravity LLC"
  true false false
  "materialise/inspect original FY2001 row and recover SOW, closeout, personnel, facility, subcontract and apparatus fields"

rezaMondaloy2020Procurement : ObjectAcquisitionReceipt
rezaMondaloy2020Procurement = object-acquisition-receipt
  "M200 Billets / Mondaloy 200 powder to HIP billets"
  "FA930020P5032"
  "SAM.gov / U.S. Air Force contract opportunity"
  primaryPublicObjectLocated
  "SAM.gov special notice; AFRL/RQRE Engine Branch, Edwards AFB; published 2020-07-07"
  "Mondaloy programme lineage / AFRL Engine Branch"
  true false false
  "recover pre-2013 predecessor contracts, cost-share work packages and programme reviews naming Reza/Hardwick/McCasland roles"

mccaslandCommandChronology : ObjectAcquisitionReceipt
mccaslandCommandChronology = object-acquisition-receipt
  "AFRL command chronology"
  "AFRL Commander 2011-05-13 through 2013-07-29"
  "official AFRL/Wright-Patterson history"
  institutionalPrimaryOnly
  "AFRL 100 Year History; Wright-Patterson change-of-command releases"
  "William Neil McCasland"
  true false false
  "find a Mondaloy-specific briefing, contract, tasking, review or approval record inside the command interval"

amyNingHistoricalReference : ObjectAcquisitionReceipt
amyNingHistoricalReference = object-acquisition-receipt
  "HAL5 2018 antigravity presentation: Ning Li & Doug Torr AC Gravity"
  "HAL5-Dec2018-Talk-AntiGravity.pdf"
  "Amy-hosted/presented historical programme reference retained in repo provenance owner"
  primaryPublicObjectLocated
  "AmyEskridgeMechanismAssociationProvenanceExact.liTorrAssociation"
  "Amy Eskridge explicitly references Ning Li/Torr work"
  true false false
  "search Amy Institute/NASA-reviewed release object, correspondence and release metadata for AC Gravity, DAAH01-01-9-R001, apparatus or personnel identity"

jplSharedWorkPackageResidual : ObjectAcquisitionReceipt
jplSharedWorkPackageResidual = object-acquisition-receipt
  "JPL Hicks/Maiwald shared-object search"
  "unresolved"
  "current public JPL science surfaces"
  searchResidual
  "Hicks small-body carriers; Maiwald SURP/action-spectroscopy carriers"
  "Michael David Hicks / Frank W. Maiwald"
  false false false
  "locate one mission, instrument, facility, procurement or work-package object naming both"

nudtSharedTaskResidual : ObjectAcquisitionReceipt
nudtSharedTaskResidual = object-acquisition-receipt
  "NUDT Chen/Feng/Zhang Daibing shared-task search"
  "unresolved"
  "current primary NUDT institutional/project surfaces"
  searchResidual
  "Galaxy/Feiteng; War Skull/decision science; UAV/autonomy programme surfaces"
  "Chen Shuming / Feng Yanghe / Zhang Daibing"
  false false false
  "locate one PLA/NUDT project, task, codebase, laboratory or work-package identifier naming two retained scientists"

currentPrimaryObjectAcquisitions : List ObjectAcquisitionReceipt
currentPrimaryObjectAcquisitions =
  ningArmyOriginalRow ∷
  rezaMondaloy2020Procurement ∷
  mccaslandCommandChronology ∷
  amyNingHistoricalReference ∷
  jplSharedWorkPackageResidual ∷
  nudtSharedTaskResidual ∷ []

primaryObjectIdentifierPaysCrossPersonH2 : Bool
primaryObjectIdentifierPaysCrossPersonH2 = false

laterProgrammePersistencePaysEarlierPersonalInvolvement : Bool
laterProgrammePersistencePaysEarlierPersonalInvolvement = false

secondaryTranscriptionPaysPrimaryCustody : Bool
secondaryTranscriptionPaysPrimaryCustody = false

historicalReferencePaysProgrammeMembership : Bool
historicalReferencePaysProgrammeMembership = false

commandAuthorityPaysSpecificProgrammeParticipation : Bool
commandAuthorityPaysSpecificProgrammeParticipation = false

currentLiteralCrossPersonSameObjectCount : Nat
currentLiteralCrossPersonSameObjectCount = 0

currentPreEventOperationalLinkCount : Nat
currentPreEventOperationalLinkCount = 0

nextPrimaryAcquisition : String
nextPrimaryAcquisition =
  "inspect original FY2001 DAAH01-01-9-R001 row/SOW/closeout; recover pre-2013 Mondaloy AFRL contract/review records; inspect Amy release object for Army/AC Gravity identifiers; then exact JPL/NUDT shared-object IDs"
