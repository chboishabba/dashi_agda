module DASHI.Culture.MissingDeceasedScientificWorkSnowballAttributionBindingsExact where

------------------------------------------------------------------------
-- COHORT SNOWBALL ATTRIBUTION BINDINGS
--
-- Thin bindings only.  Citation authority lives in the source registries and
-- source-specific owners; QID/Dewey semantics live in
-- DashiKnowledgeTraversalFunnelExact.  This file does not create another
-- ontology or another evidence model.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedScientificWorkSourceRegistryExact as Base
import DASHI.Culture.MissingDeceasedScientificWorkSourceRegistryExtendedExact as Ext
import DASHI.Culture.AmyEskridgePOAMSReviewObjectDisambiguationExact as Amy
import DASHI.Wikimedia.DashiKnowledgeTraversalFunnelExact as Traversal

------------------------------------------------------------------------
-- Primary NASA / patent / publication objects.
------------------------------------------------------------------------

amyPOAMSTMSnowballCoordinate : Ext.SnowballSourceCoordinate
amyPOAMSTMSnowballCoordinate = Ext.snowball-source-coordinate
  Amy.poamsPublicTMCitation
  Ext.primaryGovernmentRecord
  true
  (Traversal.dashi-knowledge-coordinate
    "DASHI/Culture/AmyEskridgePOAMSReviewObjectDisambiguationExact.agda"
    "NASA MSFC public POAMS Technical Memorandum object; Amy review-object identity remains separate"
    "530 Physics"
    "unresolvedQid"
    "NASA NTRS 20205010911; NASA/TM-20205010911; M-1531; NASA Subject Category 70; funding MSFC-RMB-QUANTUM-SAA8-1519855-1")
  false true true
  "Primary NASA receipt pays the public TM object and its named authors R.H. Eskridge, M.A. Nelson and M.P. Schoenfeld. Amy is not a named author; the coordinate does not weld her September-2020 review object to M-1531 or identify the Institute derivative. Funding-number namespace is not the dotted SAA annex namespace."

leblancNTRSSnowballCoordinate : Ext.SnowballSourceCoordinate
leblancNTRSSnowballCoordinate = Ext.snowball-source-coordinate
  Base.leblancNTRS2025
  Ext.primaryGovernmentRecord
  true
  (Traversal.dashi-knowledge-coordinate
    "DASHI/Physics/Nuclear/LeBlancFissionSurfacePowerICBidiExact.agda"
    "Joshua LeBlanc FSP/SNP I&C technology-maturation attribution"
    "620 Engineering"
    "unresolvedQid"
    "NASA NTRS 20250008475; WBS 658133.04.01.22.01.06")
  false true true
  "NASA/NTRS is the primary programme/publication carrier. No Joshua LeBlanc person-QID is asserted. Dewey is a broad retrieval coordinate only."

rezaPatentSnowballCoordinate : Ext.SnowballSourceCoordinate
rezaPatentSnowballCoordinate = Ext.snowball-source-coordinate
  Base.jacintoHardwickPatent2004
  Ext.primaryPatentRecord
  true
  (Traversal.dashi-knowledge-coordinate
    "DASHI/Physics/Materials/RezaBurnResistantAlloyBidiExact.agda"
    "Monica A. Jacinto / Dallis Ann Hardwick alloy inventorship"
    "620 Engineering"
    "unresolvedQid"
    "US20040208777A1; application US10/769,195; parent US20030053926A1")
  false true true
  "Patent publication identity pays co-inventorship and disclosed alloy/process claims only. It does not pay Monica Reza's event-time JPL role, sole process ownership, or later manufacturing custody."

grillmairCrossroadsSnowballCoordinate : Ext.SnowballSourceCoordinate
grillmairCrossroadsSnowballCoordinate = Ext.snowball-source-coordinate
  Base.grillmairCrossroads2017
  Ext.primaryPeerReviewedPublication
  true
  (Traversal.dashi-knowledge-coordinate
    "DASHI/Physics/Astrophysics/GrillmairStellarStreamBidiExact.agda"
    "Carl J. Grillmair stellar-stream publication attribution"
    "520 Astronomy"
    "unresolvedQid"
    "DOI 10.3847/1538-4357/aa8872; arXiv:1708.09029")
  false true true
  "DOI pays the publication object. Person QID remains unresolved here; publication identity does not create an event motive."

thomasSTINGSnowballCoordinate : Ext.SnowballSourceCoordinate
thomasSTINGSnowballCoordinate = Ext.snowball-source-coordinate
  Base.thomasSTING2018
  Ext.primaryPeerReviewedPublication
  true
  (Traversal.dashi-knowledge-coordinate
    "DASHI/Biology/JasonThomasSignallingBidiExact.agda"
    "Jason R. Thomas STING-IRF3/NFkB publication attribution"
    "570 Life sciences"
    "unresolvedQid"
    "DOI 10.1021/acschembio.7b01060; PMID 29553248; PMCID PMC5996755")
  false true true
  "DOI/PMID/PMCID identify the publication carrier and support authorship. They do not by themselves weld every Jason Thomas identity or determine event cause/manner."

loureiroViriatoSnowballCoordinate : Ext.SnowballSourceCoordinate
loureiroViriatoSnowballCoordinate = Ext.snowball-source-coordinate
  Base.loureiroViriato2016
  Ext.primaryPeerReviewedPublication
  true
  (Traversal.dashi-knowledge-coordinate
    "DASHI/Physics/Plasma/LoureiroViriatoPlasmoidBidiExact.agda"
    "Nuno F. G. Loureiro Viriato attribution"
    "530 Physics"
    "Q51287446"
    "DOI 10.1016/j.cpc.2016.05.004; arXiv:1505.02649; QID Q51287446")
  true true true
  "Verified QID is an external identity/search coordinate. DOI/publication and MIT/PSFC carriers pay the scientific attribution, not the QID."

------------------------------------------------------------------------
-- Chavez: keep institutional profile and publication identity disjoint.
------------------------------------------------------------------------

lanlAnthonyChavezSnowballCoordinate : Ext.SnowballSourceCoordinate
lanlAnthonyChavezSnowballCoordinate = Ext.snowball-source-coordinate
  Base.anthonyChavezLANL2025
  Ext.primaryInstitutionalRecord
  true
  (Traversal.dashi-knowledge-coordinate
    "DASHI/Physics/Accelerator/AnthonyChavezScorpiusBidiExact.agda"
    "Anthony Chavez LANL Summer-2025 engineering-profile identity"
    "620 Engineering"
    "unresolvedQid"
    "LANL National Security Science Summer 2025 engineering profile")
  false true true
  "This coordinate belongs to the LANL engineering-profile identity only. It must not be copied onto the missing Anthony Chavez DOB 1947-01-07 without a same-person receipt."

record ChavezCoordinateFirewall : Set where
  constructor chavez-coordinate-firewall
  field
    lanlProfileQidUnresolved : Bool
    missingPersonQidUnresolved : Bool
    sameNameMayCopyTechnicalCoordinateToMissingPerson : Bool
    publicationDoiMayMergeMarkAnthonyWithoutIdentityReceipt : Bool

canonicalChavezCoordinateFirewall : ChavezCoordinateFirewall
canonicalChavezCoordinateFirewall = chavez-coordinate-firewall
  true true false false

------------------------------------------------------------------------
-- Snowball attribution policy for all subsequent acquisition waves.
------------------------------------------------------------------------

record CohortSnowballAttributionPolicy : Set where
  constructor cohort-snowball-attribution-policy
  field
    authorOrInstitutionRecorded : Bool
    titleOrExactObjectRecorded : Bool
    strongestStableIdentifierRecorded : Bool
    doiPreferredWhenVerified : Bool
    patentOrNTRSUsedWhenNoDoiAppropriate : Bool
    primarySourceClassRecorded : Bool
    qidAddedOnlyWhenVerified : Bool
    unresolvedQidRetainedUnresolved : Bool
    deweyRecordedOnlyAsTraversalCoordinate : Bool
    secondaryRepetitionCountsAsIndependentReceipt : Bool
    qidPaysPersonIdentity : Bool
    deweyPaysSourceAuthority : Bool
    identifierPaysSameBytesAcrossVersions : Bool

canonicalCohortSnowballAttributionPolicy : CohortSnowballAttributionPolicy
canonicalCohortSnowballAttributionPolicy = cohort-snowball-attribution-policy
  true true true true true true true true true
  false false false false
