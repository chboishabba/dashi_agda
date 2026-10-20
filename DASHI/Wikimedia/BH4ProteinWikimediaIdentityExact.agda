module DASHI.Wikimedia.BH4ProteinWikimediaIdentityExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Biology.KitzerowBH4SystemNongNangMaxCutExact as BH4

------------------------------------------------------------------------
-- BH4 / WIKIDATA / WIKIPEDIA IDENTITY BRIDGE
--
-- Executed acquisition 2026-10-17:
--   16 requested; 15 unique exact P352 protein items; 1 true ambiguity (QDPR);
--   0 unresolved; 0 acquisition errors; reciprocal P702/P688 paid for every
--   acquired protein/gene relation; 7/16 direct protein-level enwiki sitelinks.
--
-- Wikimedia coordinates are identity/provenance evidence, never biochemical
-- authority.  Gene, protein, UniProt record, sequence and Wikipedia narrative
-- remain distinct objects.
------------------------------------------------------------------------

data WikimediaBiologicalEntityKind : Set where
  geneEntity : WikimediaBiologicalEntityKind
  proteinEntity : WikimediaBiologicalEntityKind
  wikipediaNarrativeEntity : WikimediaBiologicalEntityKind

data ProteinQidResolution : Set where
  uniqueExact : ProteinQidResolution
  ambiguousExact : ProteinQidResolution
  unresolvedExact : ProteinQidResolution

record WikimediaBiologyAcquisitionContract : Set where
  constructor wikimedia-biology-acquisition-contract
  field
    proteinIdentifierProperty : String
    proteinEncodedByProperty : String
    geneEncodesProperty : String
    humanTaxonQid : String
    uniqueExactProteinIdentifierRequiredForUniqueResolution : Bool
    reciprocalGeneProteinRelationRecorded : Bool
    wikidataRevisionRecorded : Bool
    wikipediaRevisionRecordedWhenAvailable : Bool
    rawResponseDigestRecorded : Bool

open WikimediaBiologyAcquisitionContract public

canonicalWikimediaBiologyAcquisitionContract : WikimediaBiologyAcquisitionContract
canonicalWikimediaBiologyAcquisitionContract =
  wikimedia-biology-acquisition-contract
    "P352" "P702" "P688" "Q5"
    true true true true true

bh4IdentityPanel : List BH4.ProteinPanelMember
bh4IdentityPanel = BH4.kitzerowBH4ProteinPanel

record AcquiredProteinQidReceipt : Set where
  constructor acquired-protein-qid-receipt
  field
    symbol : String
    accession : String
    resolution : ProteinQidResolution
    proteinQids : List String
    geneQid : String
    reciprocalP688Paid : Bool
    directEnglishWikipediaArticle : Bool
    englishWikipediaTitle : String
    exactP352Observed : Bool
    inspectionReference : String

open AcquiredProteinQidReceipt public

gch1Identity gchfrIdentity ptsIdentity sprIdentity pcbd1Identity qdprIdentity
  nos1Identity nos2Identity nos3Identity pahIdentity thIdentity tph1Identity
  tph2Identity agmoIdentity tsc2Identity mtorIdentity : AcquiredProteinQidReceipt

gch1Identity = acquired-protein-qid-receipt "GCH1" "P30793" uniqueExact ("Q1487359" ∷ []) "Q14916168" true true "GTP cyclohydrolase I" true "executed exact-P352 acquisition 2026-10-17"
gchfrIdentity = acquired-protein-qid-receipt "GCHFR" "P30047" uniqueExact ("Q21101579" ∷ []) "Q18025609" true false "" true "executed exact-P352 acquisition 2026-10-17"
ptsIdentity = acquired-protein-qid-receipt "PTS" "Q03393" uniqueExact ("Q21106788" ∷ []) "Q7121042" true false "" true "executed exact-P352 acquisition 2026-10-17"
sprIdentity = acquired-protein-qid-receipt "SPR" "P35270" uniqueExact ("Q409532" ∷ []) "Q15331000" true true "Sepiapterin reductase" true "executed exact-P352 acquisition 2026-10-17"
pcbd1Identity = acquired-protein-qid-receipt "PCBD1" "P61457" uniqueExact ("Q21204380" ∷ []) "Q18030367" true false "" true "executed exact-P352 acquisition 2026-10-17"
qdprIdentity = acquired-protein-qid-receipt "QDPR" "P09417" ambiguousExact ("Q21145902" ∷ "Q7265406" ∷ []) "Q14884995" true false "" true "two Wikidata items carry exact P352=P09417; ambiguity retained 2026-10-17"
nos1Identity = acquired-protein-qid-receipt "NOS1" "P29475" uniqueExact ("Q21121716" ∷ []) "Q18030177" true false "" true "executed exact-P352 acquisition 2026-10-17"
nos2Identity = acquired-protein-qid-receipt "NOS2" "P35228" uniqueExact ("Q21114547" ∷ []) "Q18030178" true false "" true "executed exact-P352 acquisition 2026-10-17"
nos3Identity = acquired-protein-qid-receipt "NOS3" "P29474" uniqueExact ("Q408853" ∷ []) "Q15328584" true true "Endothelial NOS" true "executed exact-P352 acquisition 2026-10-17"
pahIdentity = acquired-protein-qid-receipt "PAH" "P00439" uniqueExact ("Q420604" ∷ []) "Q14851781" true true "Phenylalanine hydroxylase" true "executed exact-P352 acquisition 2026-10-17"
thIdentity = acquired-protein-qid-receipt "TH" "P07101" uniqueExact ("Q420766" ∷ []) "Q18254977" true true "Tyrosine hydroxylase" true "executed exact-P352 acquisition 2026-10-17"
tph1Identity = acquired-protein-qid-receipt "TPH1" "P17752" uniqueExact ("Q21125451" ∷ []) "Q18032077" true false "" true "executed exact-P352 acquisition 2026-10-17"
tph2Identity = acquired-protein-qid-receipt "TPH2" "Q8IWU9" uniqueExact ("Q21125466" ∷ []) "Q18049432" true false "" true "executed exact-P352 acquisition 2026-10-17"
agmoIdentity = acquired-protein-qid-receipt "AGMO" "Q6ZNB7" uniqueExact ("Q22680132" ∷ []) "Q18057391" true false "" true "executed exact-P352 acquisition 2026-10-17"
tsc2Identity = acquired-protein-qid-receipt "TSC2" "P49815" uniqueExact ("Q21109261" ∷ []) "Q18032199" true true "TSC2" true "executed exact-P352 acquisition 2026-10-17"
mtorIdentity = acquired-protein-qid-receipt "MTOR" "P42345" uniqueExact ("Q285613" ∷ []) "Q14876086" true true "MTOR" true "executed exact-P352 acquisition 2026-10-17; Q285613 supersedes rejected preliminary seed Q21115057"

acquiredBH4WikimediaPanel : List AcquiredProteinQidReceipt
acquiredBH4WikimediaPanel =
  gch1Identity ∷ gchfrIdentity ∷ ptsIdentity ∷ sprIdentity
  ∷ pcbd1Identity ∷ qdprIdentity ∷ nos1Identity ∷ nos2Identity
  ∷ nos3Identity ∷ pahIdentity ∷ thIdentity ∷ tph1Identity
  ∷ tph2Identity ∷ agmoIdentity ∷ tsc2Identity ∷ mtorIdentity ∷ []

------------------------------------------------------------------------
-- Summary receipt from the executed JSON acquisition.
------------------------------------------------------------------------

record WikimediaPanelAcquisitionSummary : Set where
  constructor wikimedia-panel-acquisition-summary
  field
    requestedMembers : String
    verifiedUniqueMembers : String
    ambiguousMembers : String
    unresolvedMembers : String
    acquisitionErrors : String
    reciprocalEncodingPaidForEveryAcquiredMember : Bool
    directProteinEnglishWikipediaCoverage : String
    completeUniqueIdentity : Bool

open WikimediaPanelAcquisitionSummary public

canonicalWikimediaPanelAcquisitionSummary : WikimediaPanelAcquisitionSummary
canonicalWikimediaPanelAcquisitionSummary =
  wikimedia-panel-acquisition-summary
    "16" "15" "1" "0" "0" true "7/16" false

------------------------------------------------------------------------
-- Wikimedia-only cleanup frontier.  None of these obligations block the
-- already-pinned UniProt sequence identities or the independent biochemical
-- proof graph.
------------------------------------------------------------------------

data WikimediaIdentityResidual : Set where
  adjudicateQDPRDuplicateExactP352Items : WikimediaIdentityResidual
  inspectMissingProteinLevelEnwikiCoverage : WikimediaIdentityResidual

liveWikimediaIdentityResiduals : List WikimediaIdentityResidual
liveWikimediaIdentityResiduals =
  adjudicateQDPRDuplicateExactP352Items
  ∷ inspectMissingProteinLevelEnwikiCoverage
  ∷ []

qdprAmbiguityBlocksUniqueQidOnly : Bool
qdprAmbiguityBlocksUniqueQidOnly = true

missingEnwikiCoverageBlocksProteinIdentity : Bool
missingEnwikiCoverageBlocksProteinIdentity = false

------------------------------------------------------------------------
-- External-identity coordinates.  QDPR is intentionally candidate/ambiguous:
-- its gene item Q14884995 reciprocally encodes both exact-P352 protein items.
------------------------------------------------------------------------

qdprGeneQid : Identity.ExternalIdentityDemand
qdprGeneQid = Identity.mkOptionalIdentityDemand
  "BH4 Wikimedia biology identity"
  "QDPR human gene identity; P688 points to both exact P352=P09417 protein items"
  "QDPR gene"
  Identity.wikidataQid
  (Identity.verified "Q14884995" "executed acquisition inspected reciprocal P688 2026-10-17")

qdprProteinQid : Identity.ExternalIdentityDemand
qdprProteinQid = Identity.mkOptionalIdentityDemand
  "BH4 Wikimedia biology identity"
  "exact P352=P09417 protein-item resolution"
  "QDPR protein"
  Identity.wikidataQid
  (Identity.candidate "Q21145902|Q7265406" "two exact P352 matches; do not collapse without a stronger same-object witness")

------------------------------------------------------------------------
-- Cross-domain promotion boundaries.
------------------------------------------------------------------------

record WikimediaBiologyIdentityBoundary : Set where
  constructor wikimedia-biology-identity-boundary
  field
    geneQidMayBeUsedAsProteinQidWithoutP688P702Witness : Bool
    geneQidMayBeUsedAsProteinQidWithoutP688P702WitnessIsFalse : geneQidMayBeUsedAsProteinQidWithoutP688P702Witness ≡ false
    qidCreatesProteinSequenceIdentity : Bool
    qidCreatesProteinSequenceIdentityIsFalse : qidCreatesProteinSequenceIdentity ≡ false
    wikidataStatementCreatesBiologicalTruth : Bool
    wikidataStatementCreatesBiologicalTruthIsFalse : wikidataStatementCreatesBiologicalTruth ≡ false
    wikipediaNarrativeCreatesMechanisticEvidence : Bool
    wikipediaNarrativeCreatesMechanisticEvidenceIsFalse : wikipediaNarrativeCreatesMechanisticEvidence ≡ false
    wikipediaCoverageConfirmsKitzerowWholeGraph : Bool
    wikipediaCoverageConfirmsKitzerowWholeGraphIsFalse : wikipediaCoverageConfirmsKitzerowWholeGraph ≡ false
    exactP352CreatesMeasuredBH4Flux : Bool
    exactP352CreatesMeasuredBH4FluxIsFalse : exactP352CreatesMeasuredBH4Flux ≡ false
    duplicateExactP352MayBeSilentlyCollapsed : Bool
    duplicateExactP352MayBeSilentlyCollapsedIsFalse : duplicateExactP352MayBeSilentlyCollapsed ≡ false
    absentProteinEnwikiMeansProteinAbsent : Bool
    absentProteinEnwikiMeansProteinAbsentIsFalse : absentProteinEnwikiMeansProteinAbsent ≡ false
    completeReciprocalEncodingCreatesMechanisticSupport : Bool
    completeReciprocalEncodingCreatesMechanisticSupportIsFalse : completeReciprocalEncodingCreatesMechanisticSupport ≡ false

open WikimediaBiologyIdentityBoundary public

canonicalWikimediaBiologyIdentityBoundary : WikimediaBiologyIdentityBoundary
canonicalWikimediaBiologyIdentityBoundary =
  wikimedia-biology-identity-boundary
    false refl false refl false refl false refl false refl false refl
    false refl false refl false refl

canonicalBH4ProteinWikimediaIdentityReceipt : Receipt.GenericReceipt
canonicalBH4ProteinWikimediaIdentityReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 protein Wikimedia identity bridge"
    "DASHI.Wikimedia.BH4ProteinWikimediaIdentityExact"
    "executed UniProt P352 <-> Wikidata protein QID <-> P702/P688 gene relation <-> optional English-Wikipedia identity panel"
    "pins 15 unique exact protein QIDs, retains the QDPR two-item ambiguity, pays reciprocal encoding for all 16 and records the 7/16 direct protein-level enwiki coverage boundary"
    "identity coverage cannot create sequence equality, biochemical truth, BH4 flux, mechanism or whole-model confirmation; duplicate P352 items cannot be silently collapsed"
    "python3 scripts/acquire_wikimedia_bio_identity.py --kitzerow-bh4-panel && python3 scripts/check_bh4_wikimedia_identity.py"
