module DASHI.Cognition.CCDCOEP3GCC1993SourceChainExact where

------------------------------------------------------------------------
-- GCC 1993 ORIGINAL SOURCE-STAGE / TEMPORAL EVIDENCE CHAIN
--
-- Original source ownership:
-- GCC / John Shlaes owns the letters and GCC releases;
-- independent newspaper reporters own their published articles;
-- Nicky Sundt owns the archived private collection;
-- Climate Files / Climate Investigations Center owns archival
-- description and indexing, not the original GCC assertions.
-- DASHI owns only the finite type-level non-promotion results.
--
-- Archival catalogue links and independently authenticated original
-- bytes remain DIFFERENT evidence stages. No actual reporter reception,
-- audience belief change or hostile intent is established here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

data GCC1993Document : Set where
  januaryExpertiseLetter : GCC1993Document
  mayReporterLetter : GCC1993Document
  julyDepartmentOfEnergyLetter : GCC1993Document
  julyWhiteHouseLetter : GCC1993Document
  archivedMediaClippings : GCC1993Document

data ProvenanceOwner : Set where
  gccOriginalCommunicator : ProvenanceOwner
  independentArticleAuthor : ProvenanceOwner
  archivalDescription : ProvenanceOwner

data SourceRole : Set where
  addressedCommunication : SourceRole
  archivedNewsArticle : SourceRole

data CommunicationDestination : Set where
  journalists : CommunicationDestination
  energyDepartment : CommunicationDestination
  whiteHouse : CommunicationDestination
  noDocumentedAddressedRecipient : CommunicationDestination

originalRole : GCC1993Document → SourceRole
originalRole januaryExpertiseLetter = addressedCommunication
originalRole mayReporterLetter = addressedCommunication
originalRole julyDepartmentOfEnergyLetter = addressedCommunication
originalRole julyWhiteHouseLetter = addressedCommunication
originalRole archivedMediaClippings = archivedNewsArticle

originalOwner : GCC1993Document → ProvenanceOwner
originalOwner januaryExpertiseLetter = gccOriginalCommunicator
originalOwner mayReporterLetter = gccOriginalCommunicator
originalOwner julyDepartmentOfEnergyLetter = gccOriginalCommunicator
originalOwner julyWhiteHouseLetter = gccOriginalCommunicator
originalOwner archivedMediaClippings = independentArticleAuthor

addressedTo : GCC1993Document → CommunicationDestination
addressedTo januaryExpertiseLetter = journalists
addressedTo mayReporterLetter = journalists
addressedTo julyDepartmentOfEnergyLetter = energyDepartment
addressedTo julyWhiteHouseLetter = whiteHouse
addressedTo archivedMediaClippings = noDocumentedAddressedRecipient

-- Date values are ARCHIVE CATALOGUE dates, not certified send times.
-- The media-clipping collection is not assigned a single occurrence
-- time because it contains multiple independently published articles.
archiveDateYYYYMMDD : GCC1993Document → Nat
archiveDateYYYYMMDD januaryExpertiseLetter = 19930104
archiveDateYYYYMMDD mayReporterLetter = 19930503
archiveDateYYYYMMDD julyDepartmentOfEnergyLetter = 19930708
archiveDateYYYYMMDD julyWhiteHouseLetter = 19930719
archiveDateYYYYMMDD archivedMediaClippings = 0

mayReporterArchiveDate :
  archiveDateYYYYMMDD mayReporterLetter ≡ 19930503
mayReporterArchiveDate = refl

doeLetterDifferentDestination :
  addressedTo julyDepartmentOfEnergyLetter
  ≡ addressedTo mayReporterLetter → ⊥
doeLetterDifferentDestination ()

articleAuthorNotGCCHistoricalAuthor :
  originalOwner archivedMediaClippings
  ≡ originalOwner mayReporterLetter → ⊥
articleAuthorNotGCCHistoricalAuthor ()

-- The following indexed record demands separate source and
-- recipient/action receipts for one ORIGINAL case. Merely having an
-- archive listing never creates its witness.
data EvidenceStage : Set where
  archivalLocator : EvidenceStage
  independentlyReviewedOriginalBytes : EvidenceStage
  independentlyCorroboratedDelivery : EvidenceStage
  observedMediaReuse : EvidenceStage
  measuredAudienceResponse : EvidenceStage

data CandidateGrade : GCC1993Document → EvidenceStage → Set where
  catalogueOnly :
    (doc : GCC1993Document) →
    CandidateGrade doc archivalLocator

data OriginalReceipt (doc : GCC1993Document)
    : EvidenceStage → Set where
  -- Intentionally no constructors: real receipts are external inputs.
  -- An empty type is not a proof that no real-world record can exist.

record VerifiedGCCCommunication (doc : GCC1993Document) : Set where
  constructor verifiedGCCCommunication
  field
    originalBytes : OriginalReceipt doc independentlyReviewedOriginalBytes
    delivery : OriginalReceipt doc independentlyCorroboratedDelivery

record VerifiedMediaTransmission (doc : GCC1993Document) : Set where
  constructor verifiedMediaTransmission
  field
    originalAndDelivery : VerifiedGCCCommunication doc
    publishedReuse : OriginalReceipt doc observedMediaReuse

record VerifiedAudienceEffect (doc : GCC1993Document) : Set where
  constructor verifiedAudienceEffect
  field
    originalMediaTransmission : VerifiedMediaTransmission doc
    measuredEffect : OriginalReceipt doc measuredAudienceResponse

-- We have a catalogue stage for the MAY reporter mailing, but no
-- automatic promotion to delivered / media reused / audience affected.
mayReporterCatalogued : CandidateGrade mayReporterLetter archivalLocator
mayReporterCatalogued = catalogueOnly mayReporterLetter

data CatalogueEstablishesExposure : Set where
  -- No such bridge from the currently admitted catalogue facts.

catalogueDoesNotEstablishExposure :
  CatalogueEstablishesExposure → ⊥
catalogueDoesNotEstablishExposure ()

-- Stronger scientific caution: if delivery and media reuse eventually
-- become independently evidenced, hostilility/coordination is STILL a
-- distinct and source-bounded inference, not an output of these records.
