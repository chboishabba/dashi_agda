module DASHI.Promotion.DownloadedAuthorityArtifactReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.StageQuotient as StageQuotient
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Promotion.ExternalTheoremAuthoritySourceLocator as Theorem
import DASHI.Promotion.SIMetrologyExternalSourceLocator as SI

------------------------------------------------------------------------
-- Downloaded authority-source artifacts.
--
-- This module records byte-bound source evidence fetched on 2026-06-15.
-- It deliberately separates artifact custody from authority acceptance:
-- a downloaded file with a SHA-256 digest is evidence, not a constructor for
-- SI promotion, a NIST ASD spectral token, Moonshine proof authority, or a
-- Carnot/thermodynamic theorem authority.

data Empty : Set where

data DownloadedArtifactKind : Set where
  siMetrologyArtifact :
    DownloadedArtifactKind

  nistASDLocatorArtifact :
    DownloadedArtifactKind

  externalTheoremLocatorArtifact :
    DownloadedArtifactKind

record DownloadedAuthorityArtifact : Set where
  field
    artifactKind :
      DownloadedArtifactKind

    artifactLabel :
      String

    sourceUrl :
      String

    localPath :
      String

    sha256 :
      String

    byteCount :
      Nat

    accessDate :
      String

    downloadedByWget :
      Bool

    downloadedByWgetIsTrue :
      downloadedByWget ≡ true

    sha256Present :
      Bool

    sha256PresentIsTrue :
      sha256Present ≡ true

    accessDatePresent :
      Bool

    accessDatePresentIsTrue :
      accessDatePresent ≡ true

    acceptedAuthorityTokenPresent :
      Bool

    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false

    authorityPromoted :
      Bool

    authorityPromotedIsFalse :
      authorityPromoted ≡ false

open DownloadedAuthorityArtifact public

mkDownloadedArtifact :
  DownloadedArtifactKind →
  String →
  String →
  String →
  String →
  Nat →
  DownloadedAuthorityArtifact
mkDownloadedArtifact kind label url path digest bytes =
  record
    { artifactKind =
        kind
    ; artifactLabel =
        label
    ; sourceUrl =
        url
    ; localPath =
        path
    ; sha256 =
        digest
    ; byteCount =
        bytes
    ; accessDate =
        "2026-06-15"
    ; downloadedByWget =
        true
    ; downloadedByWgetIsTrue =
        refl
    ; sha256Present =
        true
    ; sha256PresentIsTrue =
        refl
    ; accessDatePresent =
        true
    ; accessDatePresentIsTrue =
        refl
    ; acceptedAuthorityTokenPresent =
        false
    ; acceptedAuthorityTokenPresentIsFalse =
        refl
    ; authorityPromoted =
        false
    ; authorityPromotedIsFalse =
        refl
    }

bipmSIBrochurePageArtifact :
  DownloadedAuthorityArtifact
bipmSIBrochurePageArtifact =
  mkDownloadedArtifact
    siMetrologyArtifact
    "BIPM SI Brochure page HTML"
    "https://www.bipm.org/en/publications/si-brochure"
    "data/authority/si_metrology_20260615/bipm_si_brochure.html"
    "ef52af47658d2f7343af8eae4897c42bac1e1400360e37136052e1eb00a8cee9"
    249461

bipmSIBrochureDOIArtifact :
  DownloadedAuthorityArtifact
bipmSIBrochureDOIArtifact =
  mkDownloadedArtifact
    siMetrologyArtifact
    "BIPM SI Brochure DOI-resolved HTML"
    "https://doi.org/10.59161/AUEZ1291"
    "data/authority/si_metrology_20260615/bipm_si_brochure_doi.html"
    "edb9b4d2dd708d46e2726f7aab5faa8ce610850d1b2b5622c60a7ead5ee16798"
    208530

bipmSIBrochureEnglishPDFArtifact :
  DownloadedAuthorityArtifact
bipmSIBrochureEnglishPDFArtifact =
  mkDownloadedArtifact
    siMetrologyArtifact
    "BIPM SI Brochure 9th edition English PDF, updated 2026"
    "https://www.bipm.org/documents/20126/41483022/SI-Brochure-9-EN.pdf/2d2b50bf-f2b4-9661-f402-5f9d66e4b507?version=7.0&t=1780410776583&download=true"
    "data/authority/si_metrology_20260615/bipm_si_brochure_9_en_2026.pdf"
    "5442eea2c680caf77a9d96879205a97f57c7c270b98a0bd0126c18fefe47e02c"
    1979202

bipmSIBrochureCompletePDFArtifact :
  DownloadedAuthorityArtifact
bipmSIBrochureCompletePDFArtifact =
  mkDownloadedArtifact
    siMetrologyArtifact
    "BIPM SI Brochure 9th edition complete PDF, updated 2026"
    "https://www.bipm.org/documents/20126/41483022/SI-Brochure-9.pdf/fcf090b2-04e6-88cc-1149-c3e029ad8232?version=6.1&t=1780473476314&download=true"
    "data/authority/si_metrology_20260615/bipm_si_brochure_9_complete_2026.pdf"
    "1122cf38e25b23d780a30607c68f7350b2b6d1f9970a89947aaa87a45ecbb20a"
    3503078

nistConstantsPageArtifact :
  DownloadedAuthorityArtifact
nistConstantsPageArtifact =
  mkDownloadedArtifact
    siMetrologyArtifact
    "NIST fundamental physical constants page"
    SI.nistCODATAConstantsUrl
    "data/authority/si_metrology_20260615/nist_constants.html"
    "e32ab53bc54ce5deca98b1edab5a1e92d9dce7a014e59ba85e79badc96eea082"
    13180

nistConstantsAllASCIIArtifact :
  DownloadedAuthorityArtifact
nistConstantsAllASCIIArtifact =
  mkDownloadedArtifact
    siMetrologyArtifact
    "NIST CODATA 2022 all-constants ASCII table"
    "https://physics.nist.gov/cuu/Constants/Table/allascii.txt"
    "data/authority/si_metrology_20260615/nist_constants_allascii_2022.txt"
    "77fb90e66c40db3e6eb16630bc9c88e4c7c8beddbe5e71be406f2f26e3f67e67"
    40801

nistSpeedOfLightSearchArtifact :
  DownloadedAuthorityArtifact
nistSpeedOfLightSearchArtifact =
  mkDownloadedArtifact
    siMetrologyArtifact
    "NIST CODATA speed of light value page"
    "https://physics.nist.gov/cgi-bin/cuu/Value?c"
    "data/authority/si_metrology_20260615/nist_constants_search_c.html"
    "b5fa91394f2ef74a5d4f4fe887f5e36e76fc3e11c6324d64f766d4a670902204"
    7722

nistPlanckSearchArtifact :
  DownloadedAuthorityArtifact
nistPlanckSearchArtifact =
  mkDownloadedArtifact
    siMetrologyArtifact
    "NIST CODATA Planck constant value page"
    "https://physics.nist.gov/cgi-bin/cuu/Value?h"
    "data/authority/si_metrology_20260615/nist_constants_search_h.html"
    "520c3aae75f75830394403ce18d6e906f6e51b82420597bc7255fc4108ab5589"
    7769

nistASDLinesFormArtifact :
  DownloadedAuthorityArtifact
nistASDLinesFormArtifact =
  mkDownloadedArtifact
    nistASDLocatorArtifact
    "NIST Atomic Spectra Database lines form"
    SI.nistASDLinesFormUrl
    "data/authority/si_metrology_20260615/nist_asd_lines_form.html"
    "fc121540f36f4c8ba59d1bb153380c4535e84a54bb95b378475ae6db27f239b5"
    51016

moonshineNotesArtifact :
  DownloadedAuthorityArtifact
moonshineNotesArtifact =
  mkDownloadedArtifact
    externalTheoremLocatorArtifact
    "Moonshine expository PDF locator source"
    "https://max.steinbergfour.com/files/moonshine.pdf"
    "data/authority/theorem_locators_20260615/moonshine_notes.pdf"
    "e109567b3240421c1cb1d77b578bc329a68d856edf956bc32ed2b8d402beba17"
    231510

carnotReflectionsArtifact :
  DownloadedAuthorityArtifact
carnotReflectionsArtifact =
  mkDownloadedArtifact
    externalTheoremLocatorArtifact
    "Carnot Reflections Gutenberg source locator"
    "https://www.gutenberg.org/files/1016/1016-h/1016-h.htm"
    "data/authority/theorem_locators_20260615/carnot_reflections_gutenberg.html"
    "7dee487a8c453b0a8fedccb7c0fef8451c00f7b74f38b46302586e0400a0d8e5"
    102530

carnotCycleWolframArtifact :
  DownloadedAuthorityArtifact
carnotCycleWolframArtifact =
  mkDownloadedArtifact
    externalTheoremLocatorArtifact
    "Carnot cycle Wolfram ScienceWorld locator"
    "https://scienceworld.wolfram.com/physics/CarnotCycle.html"
    "data/authority/theorem_locators_20260615/carnot_cycle_wolfram.html"
    "d2291e6b89cbd1abc553ee970d4ae7ada932f2c01b57666ea757cf01b5ff6595"
    11193

downloadedSIMetrologyArtifacts :
  List DownloadedAuthorityArtifact
downloadedSIMetrologyArtifacts =
  bipmSIBrochurePageArtifact
  ∷ bipmSIBrochureDOIArtifact
  ∷ bipmSIBrochureEnglishPDFArtifact
  ∷ bipmSIBrochureCompletePDFArtifact
  ∷ nistConstantsPageArtifact
  ∷ nistConstantsAllASCIIArtifact
  ∷ nistSpeedOfLightSearchArtifact
  ∷ nistPlanckSearchArtifact
  ∷ nistASDLinesFormArtifact
  ∷ []

downloadedExternalTheoremLocatorArtifacts :
  List DownloadedAuthorityArtifact
downloadedExternalTheoremLocatorArtifacts =
  moonshineNotesArtifact
  ∷ carnotReflectionsArtifact
  ∷ carnotCycleWolframArtifact
  ∷ []

record SIConstantDownloadedIngestionReceipt : Set where
  field
    constant :
      SI.Tier6SIMetrologyIntakeConstant

    constantSymbol :
      String

    sourceArtifact :
      DownloadedAuthorityArtifact

    rawTextLiteral :
      String

    rawTextLocatedInArtifact :
      Bool

    rawTextLocatedInArtifactIsTrue :
      rawTextLocatedInArtifact ≡ true

    ingestionReceiptPresent :
      Bool

    ingestionReceiptPresentIsTrue :
      ingestionReceiptPresent ≡ true

    parsedCarrierAccepted :
      Bool

    parsedCarrierAcceptedIsFalse :
      parsedCarrierAccepted ≡ false

    consumerIngestionAccepted :
      Bool

    consumerIngestionAcceptedIsFalse :
      consumerIngestionAccepted ≡ false

    acceptedAuthorityTokenPresent :
      Bool

    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false

    numericValuePromoted :
      Bool

    numericValuePromotedIsFalse :
      numericValuePromoted ≡ false

open SIConstantDownloadedIngestionReceipt public

mkDownloadedIngestionReceipt :
  SI.Tier6SIMetrologyIntakeConstant →
  String →
  String →
  SIConstantDownloadedIngestionReceipt
mkDownloadedIngestionReceipt constant symbol raw =
  record
    { constant =
        constant
    ; constantSymbol =
        symbol
    ; sourceArtifact =
        nistConstantsAllASCIIArtifact
    ; rawTextLiteral =
        raw
    ; rawTextLocatedInArtifact =
        true
    ; rawTextLocatedInArtifactIsTrue =
        refl
    ; ingestionReceiptPresent =
        true
    ; ingestionReceiptPresentIsTrue =
        refl
    ; parsedCarrierAccepted =
        false
    ; parsedCarrierAcceptedIsFalse =
        refl
    ; consumerIngestionAccepted =
        false
    ; consumerIngestionAcceptedIsFalse =
        refl
    ; acceptedAuthorityTokenPresent =
        false
    ; acceptedAuthorityTokenPresentIsFalse =
        refl
    ; numericValuePromoted =
        false
    ; numericValuePromotedIsFalse =
        refl
    }

deltaNuCsDownloadedIngestionReceipt :
  SIConstantDownloadedIngestionReceipt
deltaNuCsDownloadedIngestionReceipt =
  mkDownloadedIngestionReceipt
    SI.deltaNuCsIntake
    "Delta nu Cs"
    "hyperfine transition frequency of Cs-133                    9 192 631 770            (exact)                  Hz"

speedOfLightDownloadedIngestionReceipt :
  SIConstantDownloadedIngestionReceipt
speedOfLightDownloadedIngestionReceipt =
  mkDownloadedIngestionReceipt
    SI.speedOfLightCIntake
    "c"
    "speed of light in vacuum                                    299 792 458              (exact)                  m s^-1"

planckConstantDownloadedIngestionReceipt :
  SIConstantDownloadedIngestionReceipt
planckConstantDownloadedIngestionReceipt =
  mkDownloadedIngestionReceipt
    SI.planckConstantHIntake
    "h"
    "Planck constant                                             6.626 070 15 e-34        (exact)                  J Hz^-1"

downloadedIngestionReceipts :
  List SIConstantDownloadedIngestionReceipt
downloadedIngestionReceipts =
  deltaNuCsDownloadedIngestionReceipt
  ∷ speedOfLightDownloadedIngestionReceipt
  ∷ planckConstantDownloadedIngestionReceipt
  ∷ []

record ExternalTheoremDownloadedSourceReceipt : Set where
  field
    locatorRow :
      Theorem.ExternalTheoremAuthoritySourceLocatorRow

    stage12FibreSurfaceReceipt :
      StageQuotient.Stage12FibreSurface

    stage12FibreSurfaceReceiptIsCanonical :
      stage12FibreSurfaceReceipt ≡
      Theorem.stage12FibreSurfaceLocatorReference

    stage12FibreSurfaceCarryDepthSeamIsCanonical :
      StageQuotient.Stage12FibreSurface.carry-depth
        stage12FibreSurfaceReceipt
        Atlas.atlas-11
      ≡
      Atlas.rev-2

    stage12FibreSurfaceMatchesLocatorRow :
      stage12FibreSurfaceReceipt ≡
      Theorem.ExternalTheoremAuthoritySourceLocatorRow.stage12FibreSurfaceReceipt
        locatorRow

    sourceArtifact :
      DownloadedAuthorityArtifact

    checksumAndAccessDateBound :
      Bool

    checksumAndAccessDateBoundIsTrue :
      checksumAndAccessDateBound ≡ true

    acceptedAsProof :
      Bool

    acceptedAsProofIsFalse :
      acceptedAsProof ≡ false

    promotionPreserved :
      Bool

    promotionPreservedIsFalse :
      promotionPreserved ≡ false

open ExternalTheoremDownloadedSourceReceipt public

mkExternalTheoremDownloadedSourceReceipt :
  Theorem.ExternalTheoremAuthoritySourceLocatorRow →
  DownloadedAuthorityArtifact →
  ExternalTheoremDownloadedSourceReceipt
mkExternalTheoremDownloadedSourceReceipt row artifact =
  record
    { locatorRow =
        row
    ; stage12FibreSurfaceReceipt =
        Theorem.stage12FibreSurfaceLocatorReference
    ; stage12FibreSurfaceReceiptIsCanonical =
        refl
    ; stage12FibreSurfaceCarryDepthSeamIsCanonical =
        Theorem.stage12FibreSurfaceCarryDepthSeamLocatorWitness
    ; stage12FibreSurfaceMatchesLocatorRow =
        refl
    ; sourceArtifact =
        artifact
    ; checksumAndAccessDateBound =
        true
    ; checksumAndAccessDateBoundIsTrue =
        refl
    ; acceptedAsProof =
        false
    ; acceptedAsProofIsFalse =
        refl
    ; promotionPreserved =
        false
    ; promotionPreservedIsFalse =
        refl
    }

monsterMoonshineDownloadedSourceReceipt :
  ExternalTheoremDownloadedSourceReceipt
monsterMoonshineDownloadedSourceReceipt =
  mkExternalTheoremDownloadedSourceReceipt
    Theorem.monsterMoonshineExternalAuthorityLocatorRow
    moonshineNotesArtifact

carnotGutenbergDownloadedSourceReceipt :
  ExternalTheoremDownloadedSourceReceipt
carnotGutenbergDownloadedSourceReceipt =
  mkExternalTheoremDownloadedSourceReceipt
    Theorem.carnotThermodynamicExternalAuthorityLocatorRow
    carnotReflectionsArtifact

carnotWolframDownloadedSourceReceipt :
  ExternalTheoremDownloadedSourceReceipt
carnotWolframDownloadedSourceReceipt =
  mkExternalTheoremDownloadedSourceReceipt
    Theorem.carnotThermodynamicExternalAuthorityLocatorRow
    carnotCycleWolframArtifact

downloadedExternalTheoremSourceReceipts :
  List ExternalTheoremDownloadedSourceReceipt
downloadedExternalTheoremSourceReceipts =
  monsterMoonshineDownloadedSourceReceipt
  ∷ carnotGutenbergDownloadedSourceReceipt
  ∷ carnotWolframDownloadedSourceReceipt
  ∷ []

------------------------------------------------------------------------
-- Constructorless authority tokens: wget cannot mint these.

data AcceptedSIConstantsAuthorityToken : Set where
data AcceptedNISTASDSpectralToken : Set where
data MonsterMoonshineProofAuthorityToken : Set where
data CarnotThermodynamicTheoremAuthorityToken : Set where

acceptedSIConstantsAuthorityTokenImpossible :
  AcceptedSIConstantsAuthorityToken → Empty
acceptedSIConstantsAuthorityTokenImpossible ()

acceptedNISTASDSpectralTokenImpossible :
  AcceptedNISTASDSpectralToken → Empty
acceptedNISTASDSpectralTokenImpossible ()

monsterMoonshineProofAuthorityTokenImpossible :
  MonsterMoonshineProofAuthorityToken → Empty
monsterMoonshineProofAuthorityTokenImpossible ()

carnotThermodynamicTheoremAuthorityTokenImpossible :
  CarnotThermodynamicTheoremAuthorityToken → Empty
carnotThermodynamicTheoremAuthorityTokenImpossible ()

record DownloadedAuthorityArtifactManifest : Set where
  field
    manifestLabel :
      String

    accessDate :
      String

    siSourceArtifacts :
      List DownloadedAuthorityArtifact

    siDownloadedIngestionReceipts :
      List SIConstantDownloadedIngestionReceipt

    externalTheoremLocatorArtifacts :
      List DownloadedAuthorityArtifact

    externalTheoremDownloadedReceipts :
      List ExternalTheoremDownloadedSourceReceipt

    sourceBytesAndChecksumsRecorded :
      Bool

    sourceBytesAndChecksumsRecordedIsTrue :
      sourceBytesAndChecksumsRecorded ≡ true

    siAcceptedAuthorityTokenPresent :
      Bool

    siAcceptedAuthorityTokenPresentIsFalse :
      siAcceptedAuthorityTokenPresent ≡ false

    nistASDSpectralTokenAccepted :
      Bool

    nistASDSpectralTokenAcceptedIsFalse :
      nistASDSpectralTokenAccepted ≡ false

    monsterMoonshineProofAuthorityAccepted :
      Bool

    monsterMoonshineProofAuthorityAcceptedIsFalse :
      monsterMoonshineProofAuthorityAccepted ≡ false

    carnotThermodynamicAuthorityAccepted :
      Bool

    carnotThermodynamicAuthorityAcceptedIsFalse :
      carnotThermodynamicAuthorityAccepted ≡ false

    promotionPolicy :
      String

open DownloadedAuthorityArtifactManifest public

canonicalDownloadedAuthorityArtifactManifest :
  DownloadedAuthorityArtifactManifest
canonicalDownloadedAuthorityArtifactManifest =
  record
    { manifestLabel =
        "wget-downloaded source artifacts with SHA256/access-date receipts"
    ; accessDate =
        "2026-06-15"
    ; siSourceArtifacts =
        downloadedSIMetrologyArtifacts
    ; siDownloadedIngestionReceipts =
        downloadedIngestionReceipts
    ; externalTheoremLocatorArtifacts =
        downloadedExternalTheoremLocatorArtifacts
    ; externalTheoremDownloadedReceipts =
        downloadedExternalTheoremSourceReceipts
    ; sourceBytesAndChecksumsRecorded =
        true
    ; sourceBytesAndChecksumsRecordedIsTrue =
        refl
    ; siAcceptedAuthorityTokenPresent =
        false
    ; siAcceptedAuthorityTokenPresentIsFalse =
        refl
    ; nistASDSpectralTokenAccepted =
        false
    ; nistASDSpectralTokenAcceptedIsFalse =
        refl
    ; monsterMoonshineProofAuthorityAccepted =
        false
    ; monsterMoonshineProofAuthorityAcceptedIsFalse =
        refl
    ; carnotThermodynamicAuthorityAccepted =
        false
    ; carnotThermodynamicAuthorityAcceptedIsFalse =
        refl
    ; promotionPolicy =
        "Downloaded bytes and SHA256/access-date evidence are present; accepted authority and theorem-proof tokens remain constructorless and unpromoted"
    }

canonicalDownloadedArtifactAccessDate :
  accessDate canonicalDownloadedAuthorityArtifactManifest ≡ "2026-06-15"
canonicalDownloadedArtifactAccessDate =
  refl

canonicalDownloadedArtifactEvidenceRecorded :
  sourceBytesAndChecksumsRecorded canonicalDownloadedAuthorityArtifactManifest
  ≡
  true
canonicalDownloadedArtifactEvidenceRecorded =
  refl

canonicalSIConstantsAuthorityStillFalse :
  siAcceptedAuthorityTokenPresent canonicalDownloadedAuthorityArtifactManifest
  ≡
  false
canonicalSIConstantsAuthorityStillFalse =
  refl

canonicalNISTASDSpectralTokenStillFalse :
  nistASDSpectralTokenAccepted canonicalDownloadedAuthorityArtifactManifest
  ≡
  false
canonicalNISTASDSpectralTokenStillFalse =
  refl

canonicalMonsterMoonshineProofAuthorityStillFalse :
  monsterMoonshineProofAuthorityAccepted
    canonicalDownloadedAuthorityArtifactManifest
  ≡
  false
canonicalMonsterMoonshineProofAuthorityStillFalse =
  refl

canonicalCarnotThermodynamicAuthorityStillFalse :
  carnotThermodynamicAuthorityAccepted
    canonicalDownloadedAuthorityArtifactManifest
  ≡
  false
canonicalCarnotThermodynamicAuthorityStillFalse =
  refl
