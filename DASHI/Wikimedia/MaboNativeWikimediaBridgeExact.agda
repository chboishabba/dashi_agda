module DASHI.Wikimedia.MaboNativeWikimediaBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact as TwoOrder
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Wikimedia.IdentifierExact as Id
import DASHI.Wikimedia.NativeStatementExact as WD
import DASHI.Wikimedia.SourceProvenanceExact as Source
import DASHI.Wikimedia.ConceptEntityAlignmentExact as Align
import DASHI.Wikimedia.WikidataPNFPredicateBridgeExact as WPNF

------------------------------------------------------------------------
-- FIRST NATIVE WIKIMEDIA FIXTURE: EDDIE MABO / MABO (NO 2)
--
-- Public source calibration inspected 7 Sep 2026:
--   Wikipedia: Eddie Mabo, page id 439686; bounded permanent revision
--              oldid=1373107539 (4 Sep 2026).
--   Wikidata: Q975866 Eddie Mabo, oldid=2524901559.
--   Wikidata: Q1501525 Mabo v Queensland (No 2), oldid=2333409615.
--
-- Observed Wikidata relations used below:
--   Q975866 P31 Q5                     (Eddie Mabo instance of human)
--   Q1501525 P31 Q2334719              (Mabo No 2 instance of legal case)
--   Q1501525 P710 Q975866              (case participant Eddie Mabo)
--
-- These terms are DASHI reconstructions of bounded public source observations;
-- they are not imported Wikidata statement GUIDs and do not become legal
-- holdings, source authority, or Indigenous-law authority.
------------------------------------------------------------------------

eddieMabo : Id.ItemId
eddieMabo = Id.itemId "Q975866"

maboNo2 : Id.ItemId
maboNo2 = Id.itemId "Q1501525"

human : Id.ItemId
human = Id.itemId "Q5"

legalCase : Id.ItemId
legalCase = Id.itemId "Q2334719"

instanceOfP : Id.PropertyId
instanceOfP = Id.propertyId "P31"

participantP : Id.PropertyId
participantP = Id.propertyId "P710"

wikipediaMaboRevision : Source.WikipediaRevisionReceipt
wikipediaMaboRevision =
  Source.wikipediaRevisionReceipt
    "enwiki"
    "Eddie Mabo"
    "439686"
    "1373107539"
    "https://en.wikipedia.org/w/index.php?oldid=1373107539&title=Eddie_Mabo"
    "not-pinned-in-first-native-fixture"

wikidataEddieReceipt : Source.SourceReceipt
wikidataEddieReceipt =
  Source.sourceReceipt
    Source.wikidataStatementLayer
    "https://www.wikidata.org/w/index.php?title=Q975866&oldid=2524901559"
    "Q975866"
    "wikidata-oldid:2524901559"
    "not-pinned-in-first-native-fixture"
    "bounded Wikidata entity/statement observation; not DASHI theorem authority"

wikidataCaseReceipt : Source.SourceReceipt
wikidataCaseReceipt =
  Source.sourceReceipt
    Source.wikidataStatementLayer
    "https://www.wikidata.org/w/index.php?title=Q1501525&oldid=2333409615"
    "Q1501525"
    "wikidata-oldid:2333409615"
    "not-pinned-in-first-native-fixture"
    "bounded Wikidata case metadata observation; not the primary legal judgment"

wikipediaReceipt : Source.SourceReceipt
wikipediaReceipt =
  Source.sourceReceipt
    Source.wikipediaRevisionLayer
    "https://en.wikipedia.org/w/index.php?oldid=1373107539&title=Eddie_Mabo"
    "enwiki:439686:1373107539"
    "2026-09-04T02:39Z"
    "not-pinned-in-first-native-fixture"
    "Wikipedia prose/revision source; citations remain separate external-source fibres"

dashIReconstructionReceipt : Source.SourceReceipt
dashIReconstructionReceipt =
  Source.sourceReceipt
    Source.dashiReconstructionLayer
    "DASHI.Wikimedia.MaboNativeWikimediaBridgeExact"
    "repo-native"
    "first-native-wikimedia-fixture"
    "repository-source"
    "typed reconstruction of selected Wikimedia observations"

eddieInstanceHuman : WD.Statement
eddieInstanceHuman =
  WD.statement
    "DASHI-fixture:Q975866:P31:Q5"
    (Id.itemEntity eddieMabo)
    instanceOfP
    (WD.valueSnak (WD.entityValue (Id.itemEntity human)))
    WD.normal [] []

maboCaseInstanceLegalCase : WD.Statement
maboCaseInstanceLegalCase =
  WD.statement
    "DASHI-fixture:Q1501525:P31:Q2334719"
    (Id.itemEntity maboNo2)
    instanceOfP
    (WD.valueSnak (WD.entityValue (Id.itemEntity legalCase)))
    WD.normal [] []

maboCaseParticipantEddie : WD.Statement
maboCaseParticipantEddie =
  WD.statement
    "DASHI-fixture:Q1501525:P710:Q975866"
    (Id.itemEntity maboNo2)
    participantP
    (WD.valueSnak (WD.entityValue (Id.itemEntity eddieMabo)))
    WD.normal [] []

eddieEnglishSitelink : WD.EntitySitelink
eddieEnglishSitelink =
  WD.entitySitelink eddieMabo (WD.sitelink "enwiki" "Eddie Mabo")

eddieConcept : Align.DashiConceptRef
eddieConcept =
  Align.dashiConceptRef
    "DASHI:Mabo:EddieMaboReferent"
    "Eddie/Edward Koiki Mabo as the human referent used by the Mabo source corpus"

maboCaseConcept : Align.DashiConceptRef
maboCaseConcept =
  Align.dashiConceptRef
    "DASHI:Mabo:MaboNo2CaseReferent"
    "Mabo v Queensland (No 2) as the legal-case referent, distinct from any proposition/holding"

eddieAlignment : Align.ConceptEntityAlignment
eddieAlignment =
  Align.conceptEntityAlignment
    eddieConcept
    (Id.itemEntity eddieMabo)
    Align.sitelinkAssociation
    Align.sourceBacked
    (wikidataEddieReceipt ∷ wikipediaReceipt ∷ dashIReconstructionReceipt ∷ [])
    "referent identity only; no promotion of Wikipedia/Wikidata prose into legal authority"
    "Eddie Mabo page/QID bounded alignment"

maboCaseAlignment : Align.ConceptEntityAlignment
maboCaseAlignment =
  Align.conceptEntityAlignment
    maboCaseConcept
    (Id.itemEntity maboNo2)
    Align.directIdentifierEvidence
    Align.sourceBacked
    (wikidataCaseReceipt ∷ dashIReconstructionReceipt ∷ [])
    "legal-case identity only; holdings remain primary-authority propositions"
    "Mabo No 2 QID bounded alignment"

------------------------------------------------------------------------
-- Wikidata properties as PNF predicate candidates.
------------------------------------------------------------------------

instanceOfPredicateAlignment : WPNF.PropertyPredicateAlignment
instanceOfPredicateAlignment =
  WPNF.propertyPredicateAlignment
    instanceOfP
    PNF.contextPredicate
    "Wikimedia entity × Wikidata class"
    "Wikidata P31 instance-of relation used as a descriptive classification predicate"
    wikidataCaseReceipt
    "P31 -> PNF descriptive/context predicate; does not select legal inferential force"

participantPredicateAlignment : WPNF.PropertyPredicateAlignment
participantPredicateAlignment =
  WPNF.propertyPredicateAlignment
    participantP
    PNF.contextPredicate
    "event-or-process × participant entity"
    "Wikidata P710 participant relation used as a descriptive relational predicate"
    wikidataCaseReceipt
    "P710 -> PNF contextual relation; role and legal-party semantics require additional qualifiers/evidence"

maboParticipantPNFBridge : WPNF.StatementPredicateBridge maboCaseParticipantEddie
maboParticipantPNFBridge =
  WPNF.statement-predicate-bridge
    participantPredicateAlignment refl
    "Q1501525 P710 Q975866 projected to a PNF predicate atom under explicit property-role alignment"

maboParticipantPredicateName :
  PNF.predicateName (WPNF.statementPredicateAtom maboParticipantPNFBridge) ≡ "P710"
maboParticipantPredicateName = refl

------------------------------------------------------------------------
-- Existing Mabo constitutional/legal source architecture remains upstream and
-- independent.  Wikimedia identity metadata does not flatten the two-order
-- fibre or become a primary-authority holding.
------------------------------------------------------------------------

nativeTitleInterfaceRetained : TwoOrder.CrossOrderInterface
nativeTitleInterfaceRetained = TwoOrder.nativeTitleRecognitionInterface

data WikidataParticipantMeansPlaintiff : Set where
data WikidataCaseMetadataIsPrimaryHolding : Set where
data EddieQidCreatesIndigenousAuthority : Set where
data WikipediaNarrativeCreatesCourtHolding : Set where

participantDoesNotByItselfMeanPlaintiff : WikidataParticipantMeansPlaintiff → ⊥
participantDoesNotByItselfMeanPlaintiff ()

caseMetadataDoesNotBecomePrimaryHolding : WikidataCaseMetadataIsPrimaryHolding → ⊥
caseMetadataDoesNotBecomePrimaryHolding ()

eddieQidDoesNotCreateIndigenousAuthority : EddieQidCreatesIndigenousAuthority → ⊥
eddieQidDoesNotCreateIndigenousAuthority ()

wikipediaNarrativeDoesNotCreateCourtHolding : WikipediaNarrativeCreatesCourtHolding → ⊥
wikipediaNarrativeDoesNotCreateCourtHolding ()

record MaboNativeWikimediaBoundary : Set where
  constructor mabo-native-wikimedia-boundary
  field
    personAndCaseHaveTypedQids : Bool
    wikipediaRevisionAndWikidataStatementRemainDistinct : Bool
    p710CanProjectToPNFPredicate : Bool
    participantAutomaticallyMeansPlaintiff : Bool
    wikidataMetadataCreatesPrimaryLegalAuthority : Bool
    qidCreatesIndigenousNormativeAuthority : Bool

canonicalMaboNativeWikimediaBoundary : MaboNativeWikimediaBoundary
canonicalMaboNativeWikimediaBoundary =
  mabo-native-wikimedia-boundary true true true false false false
