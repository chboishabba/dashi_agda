module DASHI.Biology.GenBankInterpretationInteropExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Codec.GenBankLocationFiniteCore as GB
import DASHI.Codec.DNAFirstFormalism as DNA
import DASHI.Codec.DNACarrierFibre as Fibre
import DASHI.Biology.Protein.TranslationContext as Translation
import DASHI.Biology.Protein.ProteinSituatedHyperfabricExact as Situated
import DASHI.Biology.AvianMagnetoreceptionThoughtEmporiumEvidenceExact as Avian
import DASHI.Core.AttributedSourceCore as Sources
import DASHI.Cognition.PNF.WikidataRepairProposal as Repair
import DASHI.Ontology.WikidataRepairReopeningExact as Reopen
import DASHI.Interop.AvianCompassPNFSemanticBridge as PNF

------------------------------------------------------------------------
-- SOURCE-ATTRIBUTED GenBank / DASHI INTEROP
--
-- Original DNA design: Justin Atkin / The Thought Emporium,
-- Whose-gene-is-it-anyway magnetoreception GenBank file, uploaded 2020-07-04.
-- GitHub blob 0578ad167666789fbfd3faa849a455c25097b90c.
-- Repository README credits the original creator and states CC BY-SA 4.0.
--
-- This *read-only, sequence-free* module connects existing proof owners:
-- DNA alphabet, base complement, protein translation context, situated
-- protein evidence, bird magnetoreception, Wikidata repair/PNF reopening.
--
-- The 22-feature inventory was inspected from the source GitHub text.
-- The generic executable parser has NOT yet been run against the source
-- bytes in the same checked toolchain as this Agda module.
-- No protein/gene same-object, phenotype, safety, delivery or edit is proved.
------------------------------------------------------------------------

canonicalDNABaseCarrier : Set
canonicalDNABaseCarrier = DNA.Base

canonicalBaseComplementInvolutive :
  (base : DNA.Base) →
  DNA.complement (DNA.complement base) ≡ base
canonicalBaseComplementInvolutive = DNA.complement-involutive

canonicalBaseFibreCarrier : Set
canonicalBaseFibreCarrier = Fibre.BaseFibre

canonicalBaseFibreRoundTrip :
  (base : DNA.Base) →
  Fibre.decodeBaseFibre (Fibre.encodeBaseFibre base) ≡ base
canonicalBaseFibreRoundTrip = Fibre.decode-encode-base

-- Existing contextual protein owner; no default frame or isoform.
contextualProteinCodonCarrier : Set
contextualProteinCodonCarrier = Translation.Codon

contextualTranslationOwner : Set₁
contextualTranslationOwner = Translation.TranslationContext

situatedProteinOwner : Set₁
situatedProteinOwner = Situated.ProteinSituatedHyperfabric

reusableGenBankLocationOwner : Set
reusableGenBankLocationOwner = GB.Location

existingReviewOperation : Repair.RepairOperation
existingReviewOperation = Repair.holdForReview

candidateReviewCannotAssertWikidataTruth :
  Repair.RepairProposalTruthPermission Repair.proposalForReviewOnly → ⊥
candidateReviewCannotAssertWikidataTruth =
  Repair.repairProposalCannotAssertOntologyTruth

existingReopenOwner : Set
existingReopenOwner = Reopen.RepairCandidate

existingAvianPNFOwner : Set₁
existingAvianPNFOwner = PNF.AvianCompassPNFSemanticBridge

originalCreatorAttribution : Sources.AttributedSource
originalCreatorAttribution = Avian.thoughtEmporiumDigitalArchive

data GenBankAssertionTier : Set where
  authorLabelOnly : GenBankAssertionTier
  sourceBytesInspected : GenBankAssertionTier
  externalProteinLookupCandidate : GenBankAssertionTier
  ontologyIdentityForReview : GenBankAssertionTier
  independentlyValidatedBiology : GenBankAssertionTier

data GenBankInterpretationGap : Set where
  missingCDSTranslationAnnotation : GenBankInterpretationGap
  missingExplicitReadingFrame : GenBankInterpretationGap
  sourceLabelNotUniProtIdentity : GenBankInterpretationGap
  sourceLabelNotWikidataIdentity : GenBankInterpretationGap
  sourceFeatureNotObservedProtein : GenBankInterpretationGap
  sourceFeatureNotOrganismPhenotype : GenBankInterpretationGap
  unknownGeneticCodeContext : GenBankInterpretationGap
  exactOriginalBytesPythonParserPending : GenBankInterpretationGap

canonicalInterpretationGaps : List GenBankInterpretationGap
canonicalInterpretationGaps =
  missingCDSTranslationAnnotation
  ∷ missingExplicitReadingFrame
  ∷ sourceLabelNotUniProtIdentity
  ∷ sourceLabelNotWikidataIdentity
  ∷ sourceFeatureNotObservedProtein
  ∷ sourceFeatureNotOrganismPhenotype
  ∷ unknownGeneticCodeContext
  ∷ exactOriginalBytesPythonParserPending
  ∷ []

record SourceInspectionReceipt : Set where
  constructor sourceInspectionReceipt
  field
    creator : Sources.AttributedSource
    sourceFileURL : String
    gitBlobSHA : String
    sourceCommitSHA : String
    sourceInternalDate : String
    sourceGitUploadUTC : String
    sourceDeclaredBaseCount : Nat
    sourceFeatureCount : Nat
    sourceCDSCount : Nat
    circularDNAAsDeclared : Bool
    circularDNAAsDeclaredIsTrue : circularDNAAsDeclared ≡ true
    originalSequenceReproducedHere : Bool
    originalSequenceReproducedHereIsFalse :
      originalSequenceReproducedHere ≡ false
    actualOriginalPythonParseExecuted : Bool
    actualOriginalPythonParseExecutedIsFalse :
      actualOriginalPythonParseExecuted ≡ false
    CDSProteinIdentityVerified : Bool
    CDSProteinIdentityVerifiedIsFalse :
      CDSProteinIdentityVerified ≡ false
    organismMagnetoreceptionVerified : Bool
    organismMagnetoreceptionVerifiedIsFalse :
      organismMagnetoreceptionVerified ≡ false
    annotationGaps : List GenBankInterpretationGap
open SourceInspectionReceipt public

thoughtEmporiumGenBankInspection : SourceInspectionReceipt
thoughtEmporiumGenBankInspection =
  sourceInspectionReceipt
    originalCreatorAttribution
    "https://github.com/thethoughtemporium/Whose-gene-is-it-anyway/tree/master/magnetoreception"
    "0578ad167666789fbfd3faa849a455c25097b90c"
    "f83aaf2b3ada085d02d8a25cfdc4ae32c80fe09d"
    "16-JUN-2020 (GenBank LOCUS header)"
    "2020-07-04T03:23:52Z (GitHub commit)"
    11214
    22
    2
    true refl
    false refl
    false refl
    false refl
    false refl
    canonicalInterpretationGaps

sourceFeatureCountIsTwentyTwo :
  sourceFeatureCount thoughtEmporiumGenBankInspection ≡ 22
sourceFeatureCountIsTwentyTwo = refl

originalAttributionDoesNotAssertFunction :
  Sources.citationImportsProof originalCreatorAttribution ≡ false
originalAttributionDoesNotAssertFunction = refl

-- Source-derived inventory is a candidate graph, not a claimed native
-- ITIR/SensibLaw ABI or a public Wikidata repair.
data GenBankSourceRepairPermission : Set where

sourceLabelCannotAuthorizeExternalRepair :
  GenBankSourceRepairPermission → ⊥
sourceLabelCannotAuthorizeExternalRepair ()
