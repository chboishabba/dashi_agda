module DASHI.Wikimedia.IbrahimFirstLinkNovember06DecompressedVariantStrengtheningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Wikimedia.IbrahimFirstLinkNovember06ProducerPathStrengtheningExact as Prior

------------------------------------------------------------------------
-- THIN HISTORICAL-PROVENANCE STRENGTHENING
--
-- Public external receipts now independently show that the 2014-11-06 English
-- Wikipedia pages-articles family existed both as a named compressed dump and
-- as an uncompressed pages-articles XML copy in the Wikimedia ecosystem.
--
-- This aligns more closely with Ibrahim's local producer-path basename
-- `enwiki_20141106.xml`, but it still does NOT identify the exact compressed
-- variant acquired by Ibrahim, byte identity of the decompressed file, the raw
-- split command, chunk hashes, or dump -> published FLN same-object lineage.
------------------------------------------------------------------------

priorBoundary : Prior.November06StrengtheningBoundary
priorBoundary = Prior.canonicalNovember06StrengtheningBoundary

------------------------------------------------------------------------
-- Independent source receipts.
------------------------------------------------------------------------

multistream20141106Source : Attribution.AttributedSource
multistream20141106Source = Attribution.mkNoDOISource
  "Xin Jin; Wikimedia XML dumps mailing-list participants"
  "Download Multiversion Wikipedia Dataset for Research Use"
  "Wikimedia xmldatadumps-l archive"
  "2015"
  "https://lists.wikimedia.org/hyperkitty/list/xmldatadumps-l@lists.wikimedia.org/thread/UO4YJ2DYYZGVCKTMKVL7VNQTKDWZMHS4/"
  (Attribution.namedSourceKind "independent historical dump-family receipt")
  "names the 2014-11-06 English Wikipedia pages-articles-multistream XML bz2 artifact and reports a size of 11.3 GB; confirms historical artifact-family existence, not Ibrahim same-object use"
  Attribution.publicAttribution

uncompressed20141106Source : Attribution.AttributedSource
uncompressed20141106Source = Attribution.mkNoDOISource
  "Wikimedia operations / Phabricator records"
  "T122508 Prevent overly-large log files"
  "Wikimedia Phabricator"
  "2016"
  "https://phabricator.wikimedia.org/T122508"
  (Attribution.namedSourceKind "independent historical storage inventory")
  "records ./splinetools/dumps/enwiki-20141106-pages-articles.xml at approximately 48 GB on Wikimedia Labs; confirms an uncompressed pages-articles XML object existed in the Wikimedia ecosystem, not byte identity with Ibrahim's local enwiki_20141106.xml"
  Attribution.publicAttribution

------------------------------------------------------------------------
-- Variant-family receipt.
------------------------------------------------------------------------

data November06ArtifactLayer : Set where
  compressedPagesArticlesFamily : November06ArtifactLayer
  uncompressedPagesArticlesXmlFamily : November06ArtifactLayer
  ibrahimLocalRenamedXml : November06ArtifactLayer
  exactExecutedInputBytes : November06ArtifactLayer

record November06VariantReceipt : Set where
  constructor november06-variant-receipt
  field
    november06PagesArticlesFamilyExists : Bool
    multistreamCompressedArtifactExistencePaid : Bool
    uncompressedPagesArticlesXmlExistencePaid : Bool
    ibrahimLocalBasenameMatchesDateAndXmlShape : Bool
    exactCompressedVariantPaid : Bool
    decompressionProcedurePaid : Bool
    exactByteIdentityWithIbrahimLocalXmlPaid : Bool
    rawSplitCommandPaid : Bool
    chunkHashesPaid : Bool
    exactExecutedInputHashPaid : Bool
    publishedFlnSameObjectPaid : Bool
open November06VariantReceipt public

currentNovember06VariantReceipt : November06VariantReceipt
currentNovember06VariantReceipt = november06-variant-receipt
  true true true true
  false false false false false false false

------------------------------------------------------------------------
-- Non-factorability: date/family and local basename do not recover exact bytes.
------------------------------------------------------------------------

data CandidateArtifact : Set where
  sameFamilyArtifactA sameFamilyArtifactB : CandidateArtifact

data FamilySurface : Set where november06PagesArticlesSurface : FamilySurface
data ExactArtifactIdentity : Set where exactArtifactA exactArtifactB : ExactArtifactIdentity

familySurface : CandidateArtifact → FamilySurface
familySurface _ = november06PagesArticlesSurface

exactArtifactIdentity : CandidateArtifact → ExactArtifactIdentity
exactArtifactIdentity sameFamilyArtifactA = exactArtifactA
exactArtifactIdentity sameFamilyArtifactB = exactArtifactB

familyIdentityDefect : INF.NonFactorabilityWitness familySurface exactArtifactIdentity
familyIdentityDefect = INF.nonFactorabilityWitness
  sameFamilyArtifactA sameFamilyArtifactB refl (λ ())

dateAndFamilyCannotFactorExactArtifact :
  INF.FactorsThrough familySurface exactArtifactIdentity → ⊥
dateAndFamilyCannotFactorExactArtifact =
  INF.witnessRulesOutEveryFlatFactorisation familyIdentityDefect

data LocalNameCase : Set where
  sameLocalNameFromMultistream sameLocalNameFromOtherPagesArticlesVariant : LocalNameCase

data LocalNameSurface : Set where sameEnwiki20141106XmlBasename : LocalNameSurface
data UpstreamVariant : Set where multistreamUpstream otherPagesArticlesUpstream : UpstreamVariant

localNameSurface : LocalNameCase → LocalNameSurface
localNameSurface _ = sameEnwiki20141106XmlBasename

upstreamVariant : LocalNameCase → UpstreamVariant
upstreamVariant sameLocalNameFromMultistream = multistreamUpstream
upstreamVariant sameLocalNameFromOtherPagesArticlesVariant = otherPagesArticlesUpstream

localNameVariantDefect : INF.NonFactorabilityWitness localNameSurface upstreamVariant
localNameVariantDefect = INF.nonFactorabilityWitness
  sameLocalNameFromMultistream sameLocalNameFromOtherPagesArticlesVariant refl (λ ())

localBasenameCannotFactorCompressedVariant :
  INF.FactorsThrough localNameSurface upstreamVariant → ⊥
localBasenameCannotFactorCompressedVariant =
  INF.witnessRulesOutEveryFlatFactorisation localNameVariantDefect

------------------------------------------------------------------------
-- No-promotion gates.
------------------------------------------------------------------------

data ArtifactFamilyMeansSameObject : Set where
data UncompressedExistenceMeansIbrahimBytes : Set where
data MultistreamExistenceMeansIbrahimDownloadedIt : Set where
data MatchingBasenameMeansMatchingHash : Set where

artifactFamilyDoesNotCreateSameObject : ArtifactFamilyMeansSameObject → ⊥
artifactFamilyDoesNotCreateSameObject ()

uncompressedExistenceDoesNotCreateIbrahimByteIdentity :
  UncompressedExistenceMeansIbrahimBytes → ⊥
uncompressedExistenceDoesNotCreateIbrahimByteIdentity ()

multistreamExistenceDoesNotProveIbrahimAcquisition :
  MultistreamExistenceMeansIbrahimDownloadedIt → ⊥
multistreamExistenceDoesNotProveIbrahimAcquisition ()

matchingBasenameDoesNotCreateMatchingHash : MatchingBasenameMeansMatchingHash → ⊥
matchingBasenameDoesNotCreateMatchingHash ()

------------------------------------------------------------------------
-- Revised rank-1 payment.
------------------------------------------------------------------------

remainingVariantPayment : String
remainingVariantPayment =
  "2014-11-06 pages-articles family existence is now independently paid at both compressed-multistream and uncompressed-XML layers. Ibrahim's local enwiki_20141106.xml basename is therefore strongly compatible with a decompressed November-06 pages-articles artifact, but exact same-object identity remains unpaid. Recover the exact downloaded compressed variant and manifest/hash or historical bytes; recover decompression/rename receipt; hash the resulting XML; recover the raw XML-to-112 pre-split command and chunk hashes; recover external execution/custody across the true_flnetwork -> flnetwork mismatch; acquire/hash the author-hosted data/fln.json; rerun equivalently and compare output identity."

record November06DecompressedVariantBoundary : Set where
  constructor november06-decompressed-variant-boundary
  field
    pagesArticlesFamilyExistencePaid : Bool
    multistreamArtifactExistencePaid : Bool
    uncompressedXmlArtifactExistencePaid : Bool
    localProducerBasenameCompatibilityStrengthened : Bool
    exactVariantIdentityPaid : Bool
    exactByteIdentityPaid : Bool
    rawSplitLineagePaid : Bool
    outputSameObjectPaid : Bool
    nonFactorabilityRetained : Bool
open November06DecompressedVariantBoundary public

canonicalNovember06DecompressedVariantBoundary : November06DecompressedVariantBoundary
canonicalNovember06DecompressedVariantBoundary =
  november06-decompressed-variant-boundary
    true true true true false false false false true
