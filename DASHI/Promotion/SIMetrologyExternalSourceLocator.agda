module DASHI.Promotion.SIMetrologyExternalSourceLocator where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level)

------------------------------------------------------------------------
-- Tier 6 SI/CODATA/NIST external source-locator intake.
--
-- This module records checked locator/intake rows for the source facts
-- supplied to the promotion lane.  It is not an authority adapter: no
-- checksum, access-date evidence, ingestion receipt, accepted authority
-- token, or numeric promotion is present.

listCount : ∀ {a : Level} {A : Set a} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

data Tier6SIMetrologySource : Set where
  bipmSIBrochurePage : Tier6SIMetrologySource
  nistCODATAConstantsPage : Tier6SIMetrologySource
  nistASDLinesForm : Tier6SIMetrologySource

data Tier6SIMetrologyIntakeConstant : Set where
  deltaNuCsIntake : Tier6SIMetrologyIntakeConstant
  speedOfLightCIntake : Tier6SIMetrologyIntakeConstant
  planckConstantHIntake : Tier6SIMetrologyIntakeConstant

data SourceLocatorFieldKey : Set where
  sourceTierKey : SourceLocatorFieldKey
  sourceLabelKey : SourceLocatorFieldKey
  sourceUrlKey : SourceLocatorFieldKey
  sourceDoiKey : SourceLocatorFieldKey
  sourceCitationKey : SourceLocatorFieldKey
  sourceVersionFactKey : SourceLocatorFieldKey
  sourceLocatorCheckedKey : SourceLocatorFieldKey
  sourceSha256PresentKey : SourceLocatorFieldKey
  sourceAccessDatePresentKey : SourceLocatorFieldKey
  sourceAuthorityAcceptedKey : SourceLocatorFieldKey

canonicalSourceLocatorFieldKeys : List SourceLocatorFieldKey
canonicalSourceLocatorFieldKeys =
  sourceTierKey
  ∷ sourceLabelKey
  ∷ sourceUrlKey
  ∷ sourceDoiKey
  ∷ sourceCitationKey
  ∷ sourceVersionFactKey
  ∷ sourceLocatorCheckedKey
  ∷ sourceSha256PresentKey
  ∷ sourceAccessDatePresentKey
  ∷ sourceAuthorityAcceptedKey
  ∷ []

data IntakeFieldKey : Set where
  intakeConstantKey : IntakeFieldKey
  intakeSourceKey : IntakeFieldKey
  intakeRawTextKey : IntakeFieldKey
  intakeUnitTextKey : IntakeFieldKey
  intakeSourceLocatorCheckedKey : IntakeFieldKey
  intakeSha256PresentKey : IntakeFieldKey
  intakeAccessDatePresentKey : IntakeFieldKey
  intakeIngestionReceiptPresentKey : IntakeFieldKey
  intakeAcceptedAuthorityTokenPresentKey : IntakeFieldKey
  intakeNumericPromotionKey : IntakeFieldKey

canonicalIntakeFieldKeys : List IntakeFieldKey
canonicalIntakeFieldKeys =
  intakeConstantKey
  ∷ intakeSourceKey
  ∷ intakeRawTextKey
  ∷ intakeUnitTextKey
  ∷ intakeSourceLocatorCheckedKey
  ∷ intakeSha256PresentKey
  ∷ intakeAccessDatePresentKey
  ∷ intakeIngestionReceiptPresentKey
  ∷ intakeAcceptedAuthorityTokenPresentKey
  ∷ intakeNumericPromotionKey
  ∷ []

bipmSIBrochureUrl : String
bipmSIBrochureUrl =
  "https://www.bipm.org/en/publications/si-brochure"

bipmSIBrochureDoi : String
bipmSIBrochureDoi =
  "https://doi.org/10.59161/AUEZ1291"

bipmSIBrochureCitation : String
bipmSIBrochureCitation =
  "BIPM 2026 SI Brochure 9th edition"

nistCODATAConstantsUrl : String
nistCODATAConstantsUrl =
  "https://physics.nist.gov/cuu/Constants/"

nistCODATAConstantsVersionFact : String
nistCODATAConstantsVersionFact =
  "CODATA 2022 values; last data update May 2024"

nistASDLinesFormUrl : String
nistASDLinesFormUrl =
  "https://physics.nist.gov/PhysRefData/ASD/lines_form.html"

rawDeltaNuCsText : String
rawDeltaNuCsText =
  "Delta nu Cs = 9 192 631 770 Hz"

rawSpeedOfLightCText : String
rawSpeedOfLightCText =
  "c = 299 792 458 m s^-1"

rawPlanckConstantHText : String
rawPlanckConstantHText =
  "h = 6.626 070 15 e-34 J s"

record SIMetrologyExternalSourceLocatorRow : Set where
  field
    source :
      Tier6SIMetrologySource
    tierLabel :
      String
    sourceLabel :
      String
    sourceUrl :
      String
    sourceDoi :
      String
    citationText :
      String
    versionFactText :
      String
    locatorFactRecorded :
      Bool
    locatorFactRecordedIsTrue :
      locatorFactRecorded ≡ true
    sourceSha256Present :
      Bool
    sourceSha256PresentIsFalse :
      sourceSha256Present ≡ false
    sourceAccessDatePresent :
      Bool
    sourceAccessDatePresentIsFalse :
      sourceAccessDatePresent ≡ false
    sourceIngestionReceiptPresent :
      Bool
    sourceIngestionReceiptPresentIsFalse :
      sourceIngestionReceiptPresent ≡ false
    acceptedAuthorityTokenPresent :
      Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    authorityPromoted :
      Bool
    authorityPromotedIsFalse :
      authorityPromoted ≡ false
    fieldKeys :
      List SourceLocatorFieldKey
    fieldKeyCount :
      Nat
    fieldKeyCountIs10 :
      fieldKeyCount ≡ 10

open SIMetrologyExternalSourceLocatorRow public

mkSourceLocatorRow :
  Tier6SIMetrologySource →
  String →
  String →
  String →
  String →
  String →
  SIMetrologyExternalSourceLocatorRow
mkSourceLocatorRow source label url doi citation versionFact =
  record
    { source =
        source
    ; tierLabel =
        "Tier 6 SI/CODATA/NIST source locator"
    ; sourceLabel =
        label
    ; sourceUrl =
        url
    ; sourceDoi =
        doi
    ; citationText =
        citation
    ; versionFactText =
        versionFact
    ; locatorFactRecorded =
        true
    ; locatorFactRecordedIsTrue =
        refl
    ; sourceSha256Present =
        false
    ; sourceSha256PresentIsFalse =
        refl
    ; sourceAccessDatePresent =
        false
    ; sourceAccessDatePresentIsFalse =
        refl
    ; sourceIngestionReceiptPresent =
        false
    ; sourceIngestionReceiptPresentIsFalse =
        refl
    ; acceptedAuthorityTokenPresent =
        false
    ; acceptedAuthorityTokenPresentIsFalse =
        refl
    ; authorityPromoted =
        false
    ; authorityPromotedIsFalse =
        refl
    ; fieldKeys =
        canonicalSourceLocatorFieldKeys
    ; fieldKeyCount =
        listCount canonicalSourceLocatorFieldKeys
    ; fieldKeyCountIs10 =
        refl
    }

canonicalBIPMSIBrochureLocatorRow :
  SIMetrologyExternalSourceLocatorRow
canonicalBIPMSIBrochureLocatorRow =
  mkSourceLocatorRow
    bipmSIBrochurePage
    "BIPM SI Brochure page"
    bipmSIBrochureUrl
    bipmSIBrochureDoi
    bipmSIBrochureCitation
    "SI Brochure 9th edition page locator"

canonicalNISTCODATAConstantsLocatorRow :
  SIMetrologyExternalSourceLocatorRow
canonicalNISTCODATAConstantsLocatorRow =
  mkSourceLocatorRow
    nistCODATAConstantsPage
    "NIST fundamental physical constants page"
    nistCODATAConstantsUrl
    ""
    "NIST constants page"
    nistCODATAConstantsVersionFact

canonicalNISTASDLinesFormLocatorRow :
  SIMetrologyExternalSourceLocatorRow
canonicalNISTASDLinesFormLocatorRow =
  mkSourceLocatorRow
    nistASDLinesForm
    "NIST ASD lines form"
    nistASDLinesFormUrl
    ""
    "NIST Atomic Spectra Database lines form"
    "spectral-line locator form; no SI authority promotion"

record SIMetrologyExternalSourceIntakeRow : Set where
  field
    constant :
      Tier6SIMetrologyIntakeConstant
    constantSymbol :
      String
    sourceLocator :
      SIMetrologyExternalSourceLocatorRow
    sourceLocatorRef :
      String
    rawTextLiteral :
      String
    unitText :
      String
    sourceLocatorFactRecorded :
      Bool
    sourceLocatorFactRecordedIsTrue :
      sourceLocatorFactRecorded ≡ true
    sourceSha256Present :
      Bool
    sourceSha256PresentIsFalse :
      sourceSha256Present ≡ false
    accessDatePresent :
      Bool
    accessDatePresentIsFalse :
      accessDatePresent ≡ false
    ingestionReceiptPresent :
      Bool
    ingestionReceiptPresentIsFalse :
      ingestionReceiptPresent ≡ false
    acceptedAuthorityTokenPresent :
      Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    numericValuePromoted :
      Bool
    numericValuePromotedIsFalse :
      numericValuePromoted ≡ false
    fieldKeys :
      List IntakeFieldKey
    fieldKeyCount :
      Nat
    fieldKeyCountIs10 :
      fieldKeyCount ≡ 10

open SIMetrologyExternalSourceIntakeRow public

mkIntakeRow :
  Tier6SIMetrologyIntakeConstant →
  String →
  SIMetrologyExternalSourceLocatorRow →
  String →
  String →
  String →
  SIMetrologyExternalSourceIntakeRow
mkIntakeRow constant symbol locator locatorRef raw unit =
  record
    { constant =
        constant
    ; constantSymbol =
        symbol
    ; sourceLocator =
        locator
    ; sourceLocatorRef =
        locatorRef
    ; rawTextLiteral =
        raw
    ; unitText =
        unit
    ; sourceLocatorFactRecorded =
        true
    ; sourceLocatorFactRecordedIsTrue =
        refl
    ; sourceSha256Present =
        false
    ; sourceSha256PresentIsFalse =
        refl
    ; accessDatePresent =
        false
    ; accessDatePresentIsFalse =
        refl
    ; ingestionReceiptPresent =
        false
    ; ingestionReceiptPresentIsFalse =
        refl
    ; acceptedAuthorityTokenPresent =
        false
    ; acceptedAuthorityTokenPresentIsFalse =
        refl
    ; numericValuePromoted =
        false
    ; numericValuePromotedIsFalse =
        refl
    ; fieldKeys =
        canonicalIntakeFieldKeys
    ; fieldKeyCount =
        listCount canonicalIntakeFieldKeys
    ; fieldKeyCountIs10 =
        refl
    }

canonicalDeltaNuCsIntakeRow :
  SIMetrologyExternalSourceIntakeRow
canonicalDeltaNuCsIntakeRow =
  mkIntakeRow
    deltaNuCsIntake
    "Delta nu Cs"
    canonicalBIPMSIBrochureLocatorRow
    "canonicalBIPMSIBrochureLocatorRow"
    rawDeltaNuCsText
    "Hz"

canonicalSpeedOfLightCIntakeRow :
  SIMetrologyExternalSourceIntakeRow
canonicalSpeedOfLightCIntakeRow =
  mkIntakeRow
    speedOfLightCIntake
    "c"
    canonicalBIPMSIBrochureLocatorRow
    "canonicalBIPMSIBrochureLocatorRow"
    rawSpeedOfLightCText
    "m s^-1"

canonicalPlanckConstantHIntakeRow :
  SIMetrologyExternalSourceIntakeRow
canonicalPlanckConstantHIntakeRow =
  mkIntakeRow
    planckConstantHIntake
    "h"
    canonicalBIPMSIBrochureLocatorRow
    "canonicalBIPMSIBrochureLocatorRow"
    rawPlanckConstantHText
    "J s"

record SIMetrologyExternalSourceLocatorManifest : Set₁ where
  field
    manifestLabel :
      String
    tierLabel :
      String
    sourceLocatorRows :
      List SIMetrologyExternalSourceLocatorRow
    sourceLocatorRowCount :
      Nat
    sourceLocatorRowCountIs3 :
      sourceLocatorRowCount ≡ 3
    intakeRows :
      List SIMetrologyExternalSourceIntakeRow
    intakeRowCount :
      Nat
    intakeRowCountIs3 :
      intakeRowCount ≡ 3
    bipmLocatorRow :
      SIMetrologyExternalSourceLocatorRow
    nistCODATALocatorRow :
      SIMetrologyExternalSourceLocatorRow
    nistASDLocatorRow :
      SIMetrologyExternalSourceLocatorRow
    deltaNuCsRow :
      SIMetrologyExternalSourceIntakeRow
    cRow :
      SIMetrologyExternalSourceIntakeRow
    hRow :
      SIMetrologyExternalSourceIntakeRow
    policyText :
      String
    allSourceSha256Present :
      Bool
    allSourceSha256PresentIsFalse :
      allSourceSha256Present ≡ false
    anyAccessDatePresent :
      Bool
    anyAccessDatePresentIsFalse :
      anyAccessDatePresent ≡ false
    anyIngestionReceiptPresent :
      Bool
    anyIngestionReceiptPresentIsFalse :
      anyIngestionReceiptPresent ≡ false
    anyAcceptedAuthorityTokenPresent :
      Bool
    anyAcceptedAuthorityTokenPresentIsFalse :
      anyAcceptedAuthorityTokenPresent ≡ false
    anyAuthorityPromoted :
      Bool
    anyAuthorityPromotedIsFalse :
      anyAuthorityPromoted ≡ false

open SIMetrologyExternalSourceLocatorManifest public

canonicalSourceLocatorRows :
  List SIMetrologyExternalSourceLocatorRow
canonicalSourceLocatorRows =
  canonicalBIPMSIBrochureLocatorRow
  ∷ canonicalNISTCODATAConstantsLocatorRow
  ∷ canonicalNISTASDLinesFormLocatorRow
  ∷ []

canonicalIntakeRows :
  List SIMetrologyExternalSourceIntakeRow
canonicalIntakeRows =
  canonicalDeltaNuCsIntakeRow
  ∷ canonicalSpeedOfLightCIntakeRow
  ∷ canonicalPlanckConstantHIntakeRow
  ∷ []

canonicalSIMetrologyExternalSourceLocatorManifest :
  SIMetrologyExternalSourceLocatorManifest
canonicalSIMetrologyExternalSourceLocatorManifest =
  record
    { manifestLabel =
        "Tier 6 SI/CODATA/NIST source-locator intake manifest"
    ; tierLabel =
        "Tier 6"
    ; sourceLocatorRows =
        canonicalSourceLocatorRows
    ; sourceLocatorRowCount =
        listCount canonicalSourceLocatorRows
    ; sourceLocatorRowCountIs3 =
        refl
    ; intakeRows =
        canonicalIntakeRows
    ; intakeRowCount =
        listCount canonicalIntakeRows
    ; intakeRowCountIs3 =
        refl
    ; bipmLocatorRow =
        canonicalBIPMSIBrochureLocatorRow
    ; nistCODATALocatorRow =
        canonicalNISTCODATAConstantsLocatorRow
    ; nistASDLocatorRow =
        canonicalNISTASDLinesFormLocatorRow
    ; deltaNuCsRow =
        canonicalDeltaNuCsIntakeRow
    ; cRow =
        canonicalSpeedOfLightCIntakeRow
    ; hRow =
        canonicalPlanckConstantHIntakeRow
    ; policyText =
        "locator facts and raw literals only; SHA, access-date, ingestion, authority acceptance, and promotion remain false"
    ; allSourceSha256Present =
        false
    ; allSourceSha256PresentIsFalse =
        refl
    ; anyAccessDatePresent =
        false
    ; anyAccessDatePresentIsFalse =
        refl
    ; anyIngestionReceiptPresent =
        false
    ; anyIngestionReceiptPresentIsFalse =
        refl
    ; anyAcceptedAuthorityTokenPresent =
        false
    ; anyAcceptedAuthorityTokenPresentIsFalse =
        refl
    ; anyAuthorityPromoted =
        false
    ; anyAuthorityPromotedIsFalse =
        refl
    }

canonicalBIPMUrlIsSuppliedLocator :
  SIMetrologyExternalSourceLocatorRow.sourceUrl
    canonicalBIPMSIBrochureLocatorRow
  ≡ bipmSIBrochureUrl
canonicalBIPMUrlIsSuppliedLocator = refl

canonicalBIPMDoiIsSuppliedLocator :
  SIMetrologyExternalSourceLocatorRow.sourceDoi
    canonicalBIPMSIBrochureLocatorRow
  ≡ bipmSIBrochureDoi
canonicalBIPMDoiIsSuppliedLocator = refl

canonicalNISTConstantsVersionFactIsSupplied :
  SIMetrologyExternalSourceLocatorRow.versionFactText
    canonicalNISTCODATAConstantsLocatorRow
  ≡ nistCODATAConstantsVersionFact
canonicalNISTConstantsVersionFactIsSupplied = refl

canonicalNISTASDUrlIsSuppliedLocator :
  SIMetrologyExternalSourceLocatorRow.sourceUrl
    canonicalNISTASDLinesFormLocatorRow
  ≡ nistASDLinesFormUrl
canonicalNISTASDUrlIsSuppliedLocator = refl

canonicalDeltaNuCsRawTextIsLiteral :
  SIMetrologyExternalSourceIntakeRow.rawTextLiteral
    canonicalDeltaNuCsIntakeRow
  ≡ rawDeltaNuCsText
canonicalDeltaNuCsRawTextIsLiteral = refl

canonicalCRawTextIsLiteral :
  SIMetrologyExternalSourceIntakeRow.rawTextLiteral
    canonicalSpeedOfLightCIntakeRow
  ≡ rawSpeedOfLightCText
canonicalCRawTextIsLiteral = refl

canonicalHRawTextIsLiteral :
  SIMetrologyExternalSourceIntakeRow.rawTextLiteral
    canonicalPlanckConstantHIntakeRow
  ≡ rawPlanckConstantHText
canonicalHRawTextIsLiteral = refl

canonicalManifestAuthorityPromotedIsFalse :
  SIMetrologyExternalSourceLocatorManifest.anyAuthorityPromoted
    canonicalSIMetrologyExternalSourceLocatorManifest
  ≡ false
canonicalManifestAuthorityPromotedIsFalse = refl
