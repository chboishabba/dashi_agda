module DASHI.Wikimedia.BH4ProteinWikimediaIdentityExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Biology.KitzerowBH4SystemNongNangMaxCutExact as BH4

------------------------------------------------------------------------
-- BH4 / WIKIDATA / WIKIPEDIA IDENTITY BRIDGE
--
-- This module reuses SnowballExternalIdentityAvailabilityExact rather than
-- inventing a biology-local QID ontology.  Wikimedia coordinates help reconcile
-- public entities with the exact UniProt panel, but they are not biochemical
-- evidence.  In particular, human gene items and protein items are different
-- objects: the intended path is
--
--   gene QID --P688 encodes--> protein QID --P352 UniProt protein ID--> accession
--            <--P702 encoded by--
--
-- English-Wikipedia page/revision coordinates are additional provenance only.
-- The executable acquisition owner is scripts/acquire_wikimedia_bio_identity.py.
------------------------------------------------------------------------

data WikimediaBiologicalEntityKind : Set where
  geneEntity : WikimediaBiologicalEntityKind
  proteinEntity : WikimediaBiologicalEntityKind
  wikipediaNarrativeEntity : WikimediaBiologicalEntityKind

record WikimediaBiologyAcquisitionContract : Set where
  constructor wikimedia-biology-acquisition-contract
  field
    proteinIdentifierProperty : String
    proteinEncodedByProperty : String
    geneEncodesProperty : String
    humanTaxonQid : String
    uniqueExactProteinIdentifierRequired : Bool
    reciprocalGeneProteinRelationRecordedWhenAvailable : Bool
    wikidataRevisionRecorded : Bool
    wikipediaRevisionRecordedWhenAvailable : Bool
    rawResponseDigestRecorded : Bool

open WikimediaBiologyAcquisitionContract public

canonicalWikimediaBiologyAcquisitionContract : WikimediaBiologyAcquisitionContract
canonicalWikimediaBiologyAcquisitionContract =
  wikimedia-biology-acquisition-contract
    "P352"
    "P702"
    "P688"
    "Q5"
    true true true true true

------------------------------------------------------------------------
-- The exact panel is reused from the biology max-cut; no duplicate accession
-- list is introduced here.
------------------------------------------------------------------------

bh4IdentityPanel : List BH4.ProteinPanelMember
bh4IdentityPanel = BH4.kitzerowBH4ProteinPanel

record ProteinQidSeed : Set where
  constructor protein-qid-seed
  field
    symbol : String
    accession : String
    proteinQid : String
    inspectionReference : String
    exactP352Observed : Bool
    qidCreatesSequenceIdentity : Bool
    qidCreatesBiologicalTruth : Bool

open ProteinQidSeed public

-- Publicly inspected protein-item seeds.  The acquisition script is the
-- authoritative mechanism for resolving/rechecking the complete 16-member
-- panel and pinning current revisions.
gch1ProteinSeed : ProteinQidSeed
gch1ProteinSeed = protein-qid-seed
  "GCH1" "P30793" "Q1487359"
  "Wikidata GTP cyclohydrolase 1 protein item; exact P352=P30793 inspected 2026-10-17"
  true false false

sprProteinSeed : ProteinQidSeed
sprProteinSeed = protein-qid-seed
  "SPR" "P35270" "Q409532"
  "Wikidata sepiapterin reductase protein item; exact P352=P35270 inspected 2026-10-17"
  true false false

pahProteinSeed : ProteinQidSeed
pahProteinSeed = protein-qid-seed
  "PAH" "P00439" "Q420604"
  "Wikidata phenylalanine hydroxylase protein item; exact P352=P00439 inspected 2026-10-17"
  true false false

thProteinSeed : ProteinQidSeed
thProteinSeed = protein-qid-seed
  "TH" "P07101" "Q420766"
  "Wikidata tyrosine hydroxylase protein item; exact P352=P07101 inspected 2026-10-17"
  true false false

mtorProteinSeed : ProteinQidSeed
mtorProteinSeed = protein-qid-seed
  "MTOR" "P42345" "Q21115057"
  "Wikidata mechanistic target of rapamycin kinase protein item; exact P352=P42345 inspected 2026-10-17"
  true false false

knownProteinSeeds : List ProteinQidSeed
knownProteinSeeds =
  gch1ProteinSeed ∷ sprProteinSeed ∷ pahProteinSeed ∷ thProteinSeed ∷ mtorProteinSeed ∷ []

------------------------------------------------------------------------
-- Gene-QID examples deliberately remain gene identities rather than being
-- reused as protein QIDs.
------------------------------------------------------------------------

qdprGeneQid : Identity.ExternalIdentityDemand
qdprGeneQid = Identity.mkOptionalIdentityDemand
  "BH4 Wikimedia biology identity"
  "QDPR human gene identity; P688 encodes protein carrying UniProt P09417"
  "QDPR gene"
  Identity.wikidataQid
  (Identity.verified "Q14884995" "Wikidata gene item inspected 2026-10-17")

qdprProteinQid : Identity.ExternalIdentityDemand
qdprProteinQid = Identity.mkOptionalIdentityDemand
  "BH4 Wikimedia biology identity"
  "exact P352=P09417 protein-item resolution"
  "QDPR protein"
  Identity.wikidataQid
  (Identity.unresolved "gene Q14884995 is not promoted to protein identity; resolve exact P352 by acquisition script")

pcbd1GeneQid : Identity.ExternalIdentityDemand
pcbd1GeneQid = Identity.mkOptionalIdentityDemand
  "BH4 Wikimedia biology identity"
  "PCBD1 human gene identity; P688 encodes protein carrying UniProt P61457"
  "PCBD1 gene"
  Identity.wikidataQid
  (Identity.verified "Q18030367" "Wikidata gene item inspected 2026-10-17")

nos1GeneQid : Identity.ExternalIdentityDemand
nos1GeneQid = Identity.mkOptionalIdentityDemand
  "BH4 Wikimedia biology identity"
  "NOS1 human gene identity; P688 encodes protein carrying UniProt P29475"
  "NOS1 gene"
  Identity.wikidataQid
  (Identity.verified "Q18030177" "Wikidata gene item inspected 2026-10-17")

------------------------------------------------------------------------
-- Cross-domain promotion boundaries.
------------------------------------------------------------------------

record WikimediaBiologyIdentityBoundary : Set where
  constructor wikimedia-biology-identity-boundary
  field
    geneQidMayBeUsedAsProteinQidWithoutP688P702Witness : Bool
    geneQidMayBeUsedAsProteinQidWithoutP688P702WitnessIsFalse :
      geneQidMayBeUsedAsProteinQidWithoutP688P702Witness ≡ false
    qidCreatesProteinSequenceIdentity : Bool
    qidCreatesProteinSequenceIdentityIsFalse :
      qidCreatesProteinSequenceIdentity ≡ false
    wikidataStatementCreatesBiologicalTruth : Bool
    wikidataStatementCreatesBiologicalTruthIsFalse :
      wikidataStatementCreatesBiologicalTruth ≡ false
    wikipediaNarrativeCreatesMechanisticEvidence : Bool
    wikipediaNarrativeCreatesMechanisticEvidenceIsFalse :
      wikipediaNarrativeCreatesMechanisticEvidence ≡ false
    wikipediaCoverageConfirmsKitzerowWholeGraph : Bool
    wikipediaCoverageConfirmsKitzerowWholeGraphIsFalse :
      wikipediaCoverageConfirmsKitzerowWholeGraph ≡ false
    exactP352CreatesMeasuredBH4Flux : Bool
    exactP352CreatesMeasuredBH4FluxIsFalse :
      exactP352CreatesMeasuredBH4Flux ≡ false
    unresolvedProteinQidMeansProteinAbsent : Bool
    unresolvedProteinQidMeansProteinAbsentIsFalse :
      unresolvedProteinQidMeansProteinAbsent ≡ false

open WikimediaBiologyIdentityBoundary public

canonicalWikimediaBiologyIdentityBoundary : WikimediaBiologyIdentityBoundary
canonicalWikimediaBiologyIdentityBoundary =
  wikimedia-biology-identity-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

canonicalBH4ProteinWikimediaIdentityReceipt : Receipt.GenericReceipt
canonicalBH4ProteinWikimediaIdentityReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 protein Wikimedia identity bridge"
    "DASHI.Wikimedia.BH4ProteinWikimediaIdentityExact"
    "UniProt accession <-> exact Wikidata P352 protein item <-> P702/P688 gene relation <-> optional English-Wikipedia page/revision"
    "reuses the repository external-identity/QID surface and the exact 16-protein BH4 panel without collapsing gene, protein, sequence, narrative or mechanism identities"
    "QIDs and Wikipedia pages are provenance/identity coordinates; they do not create sequence equality, biological truth, measured BH4 flux, mechanism or whole-model confirmation"
    "python3 scripts/acquire_wikimedia_bio_identity.py --kitzerow-bh4-panel && agda -i . DASHI/Wikimedia/BH4ProteinWikimediaIdentityExact.agda"
