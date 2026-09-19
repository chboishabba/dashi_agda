module DASHI.Culture.MissingDeceasedLiteralObjectEvidenceLadderExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LITERAL OBJECT / PROGRAMME EVIDENCE LADDER
--
-- This layer separates: a person explicitly referring to another person's
-- work; a literal object/programme identifier attached to one person; a
-- literal identifier connecting two retained people to the same programme;
-- and a pre-event operational linkage.  No lower rung promotes itself.
------------------------------------------------------------------------

data ObjectEvidenceClass : Set where
  thematicAdjacency : ObjectEvidenceClass
  personReference : ObjectEvidenceClass
  institutionIdentifier : ObjectEvidenceClass
  programmeObjectIdentifier : ObjectEvidenceClass
  intermediatedProgrammeChain : ObjectEvidenceClass
  crossPersonSameProgramme : ObjectEvidenceClass
  preEventOperationalLink : ObjectEvidenceClass

record LiteralObjectEvidenceReceipt : Set where
  constructor literal-object-evidence-receipt
  field
    receiptName : String
    participantA : String
    participantB : String
    objectOrIdentifier : String
    evidenceClass : ObjectEvidenceClass
    sourceReference : String
    primarySourceState : String
    literalObjectPaid : Bool
    literalCrossPersonPaid : Bool
    preEventOperationalPaid : Bool
    whatItPays : String
    whatItCannotPay : String
    nextExactLeaf : String

open LiteralObjectEvidenceReceipt public

ningArmyAgreementReceipt : LiteralObjectEvidenceReceipt
ningArmyAgreementReceipt = literal-object-evidence-receipt
  "Ning Li / AC Gravity Army prototype agreement"
  "Ning Li / AC Gravity LLC"
  "no second retained scientist yet welded"
  "DAAH01-01-9-R001; Gravito - Electro Magnetic Superconductivity Experiment; AMCOM AMSAM-AC-RD-BA"
  programmeObjectIdentifier
  "DoD FY2001 Annual Report on Cooperative Agreements and Other Transactions under 10 USC 2371, archived locator: https://web.archive.org/web/20210801183915id_/https://www.acq.osd.mil/dpap/Docs/FY01RPT.doc"
  "primary report locator identified; original legacy-DOC bytes/page-66 row not independently retained in DASHI; SOW/closeout/result still acquisition debt"
  true false false
  "pays a literal Army programme/object identifier associated with AC Gravity and the named gravito-electromagnetic superconductivity experiment"
  "does not pay successful result, technical completion, classification, a second retained scientist, or coordinated targeting"
  "acquire original FY2001 row bytes plus SOW/closeout; enumerate named personnel, subcontractors, facilities and apparatus identifiers"

rezaMondaloyProcurementReceipt : LiteralObjectEvidenceReceipt
rezaMondaloyProcurementReceipt = literal-object-evidence-receipt
  "AFRL Mondaloy 200 later procurement"
  "Monica Jacinto / Monica Reza materials lineage"
  "William Neil McCasland not named on this procurement"
  "FA930020P5032; M200 Billets; Mondaloy 200 powder -> hot-isostatically-pressed billets"
  programmeObjectIdentifier
  "SAM.gov Special Notice FA930020P5032, Air Force Test Center / AFRL Engine Branch (AFRL/RQRE), published 2020-07-07"
  "primary federal procurement notice publicly accessible"
  true false false
  "pays persistent Air Force/AFRL handling of Mondaloy 200 as a specific material object and process transformation"
  "2020 procurement cannot retroactively establish McCasland involvement during his 2011-2013 AFRL command and does not name Reza on the procurement notice"
  "recover pre-2013 AFRL Mondaloy contract/work-package identifiers, programme reviews and named participants; bridge composition/process identity back to Reza/Hardwick patents"

amyNingHistoricalReferenceReceipt : LiteralObjectEvidenceReceipt
amyNingHistoricalReferenceReceipt = literal-object-evidence-receipt
  "Amy Eskridge explicit historical reference to Ning Li/Torr"
  "Amy Eskridge"
  "Ning Li"
  "HAL5-Dec2018-Talk-AntiGravity.pdf slide: Ning Li & Doug Torr AC Gravity (1990s)"
  personReference
  "DASHI.Culture.AmyEskridgeMechanismAssociationProvenanceExact.liTorrAssociation / HAL5-hosted 2018 presentation"
  "official/source-entitled presentation carrier already formalised in-repo"
  true false false
  "pays that Amy explicitly knew and discussed Ning Li/Torr/AC Gravity work as historical antigravity research"
  "does not pay shared team membership, contract, apparatus, funding, custody, or a causal/event link"
  "search Amy Institute/NASA-reviewed object and associated release records for AC Gravity, DAAH01-01-9-R001, apparatus, personnel or successor-programme identifiers"

rezaHardwickAfrlIntermediatedReceipt : LiteralObjectEvidenceReceipt
rezaHardwickAfrlIntermediatedReceipt = literal-object-evidence-receipt
  "Reza-Hardwick-AFRL intermediary chain"
  "Monica Jacinto / Monica Reza"
  "William Neil McCasland"
  "Reza/Jacinto co-invention with Dallis Hardwick -> Hardwick later AFRL advanced-gas-turbine materials leadership -> McCasland later AFRL command"
  intermediatedProgrammeChain
  "public patent/inventor lineage; UNSW Hardwick career profile; official AFRL McCasland chronology"
  "individual links are source-backed; no single same-work-package source naming Reza and McCasland has been acquired"
  false false false
  "pays an institutionally plausible intermediary path worth targeted archival search"
  "does not pay a direct professional relation or same Mondaloy contract/work package between Reza and McCasland"
  "recover exact AFRL Mondaloy programme reviews/contracts from 1999-2013 and inspect named leadership/technical participants"

currentLiteralObjectEvidence : List LiteralObjectEvidenceReceipt
currentLiteralObjectEvidence =
  ningArmyAgreementReceipt ∷
  rezaMondaloyProcurementReceipt ∷
  amyNingHistoricalReferenceReceipt ∷
  rezaHardwickAfrlIntermediatedReceipt ∷ []

literalProgrammeObjectIdentifierCount : Nat
literalProgrammeObjectIdentifierCount = 2

literalPersonReferenceCount : Nat
literalPersonReferenceCount = 1

literalCrossPersonSameProgrammeCount : Nat
literalCrossPersonSameProgrammeCount = 0

preEventOperationalLinkCount : Nat
preEventOperationalLinkCount = 0

personReferencePaysSameProgramme : Bool
personReferencePaysSameProgramme = false

programmeIdentifierPaysCrossPersonLink : Bool
programmeIdentifierPaysCrossPersonLink = false

laterProcurementPaysEarlierCommandInvolvement : Bool
laterProcurementPaysEarlierCommandInvolvement = false

intermediatedInstitutionalChainPaysDirectRelation : Bool
intermediatedInstitutionalChainPaysDirectRelation = false

literalObjectReceiptPaysEventCause : Bool
literalObjectReceiptPaysEventCause = false

preEventOperationalEvidenceStillRequiredForH3 : Bool
preEventOperationalEvidenceStillRequiredForH3 = true
