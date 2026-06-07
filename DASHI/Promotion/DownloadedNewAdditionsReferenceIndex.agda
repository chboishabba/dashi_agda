module DASHI.Promotion.DownloadedNewAdditionsReferenceIndex where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_; _++_)

------------------------------------------------------------------------
-- Downloaded new-additions reference index.
--
-- This module records the local downloaded context artifacts under
-- temp-DOWNLOADED/new additions.  The purpose is source intake and routing:
-- these artifacts may support future Hodge/Maxwell/YM/SM/chemistry/context
-- work, but this receipt does not accept theorem authority, empirical
-- authority, or promotion for any lane.

listCount : {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

------------------------------------------------------------------------
-- Artifact taxonomy.

data DownloadedArtifactFormat : Set where
  pdfArtifact :
    DownloadedArtifactFormat

  imageArtifact :
    DownloadedArtifactFormat

  dataArtifact :
    DownloadedArtifactFormat

  codeArtifact :
    DownloadedArtifactFormat

  htmlArtifact :
    DownloadedArtifactFormat

formatLabel :
  DownloadedArtifactFormat →
  String
formatLabel pdfArtifact =
  "PDF/context document"
formatLabel imageArtifact =
  "image/plot"
formatLabel dataArtifact =
  "CSV/JSON data artifact"
formatLabel codeArtifact =
  "code/formal artifact"
formatLabel htmlArtifact =
  "HTML planning artifact"

data DownloadedArtifactFamily : Set where
  hodgeGRContext :
    DownloadedArtifactFamily

  quantumSMChemistryContext :
    DownloadedArtifactFamily

  constantsAndMeasurementContext :
    DownloadedArtifactFamily

  ymClaySprintContext :
    DownloadedArtifactFamily

  visualizationContext :
    DownloadedArtifactFamily

familyLabel :
  DownloadedArtifactFamily →
  String
familyLabel hodgeGRContext =
  "Hodge/GR/MDL context"
familyLabel quantumSMChemistryContext =
  "quantum/SM/chemistry context"
familyLabel constantsAndMeasurementContext =
  "constants/measurement context"
familyLabel ymClaySprintContext =
  "Yang-Mills Clay sprint context"
familyLabel visualizationContext =
  "visualization/context figure"

record DownloadedArtifactRow : Set where
  field
    artifactFormat :
      DownloadedArtifactFormat

    artifactFormatText :
      String

    artifactFormatTextIsCanonical :
      artifactFormatText ≡ formatLabel artifactFormat

    artifactFamily :
      DownloadedArtifactFamily

    artifactFamilyText :
      String

    artifactFamilyTextIsCanonical :
      artifactFamilyText ≡ familyLabel artifactFamily

    artifactPath :
      String

    intakeRole :
      String

    theoremAuthority :
      Bool

    theoremAuthorityIsFalse :
      theoremAuthority ≡ false

    empiricalAuthority :
      Bool

    empiricalAuthorityIsFalse :
      empiricalAuthority ≡ false

    promotesLane :
      Bool

    promotesLaneIsFalse :
      promotesLane ≡ false

open DownloadedArtifactRow public

mkDownloadedArtifactRow :
  DownloadedArtifactFormat →
  DownloadedArtifactFamily →
  String →
  String →
  DownloadedArtifactRow
mkDownloadedArtifactRow format family path role =
  record
    { artifactFormat = format
    ; artifactFormatText = formatLabel format
    ; artifactFormatTextIsCanonical = refl
    ; artifactFamily = family
    ; artifactFamilyText = familyLabel family
    ; artifactFamilyTextIsCanonical = refl
    ; artifactPath = path
    ; intakeRole = role
    ; theoremAuthority = false
    ; theoremAuthorityIsFalse = refl
    ; empiricalAuthority = false
    ; empiricalAuthorityIsFalse = refl
    ; promotesLane = false
    ; promotesLaneIsFalse = refl
    }

basePath :
  String
basePath =
  "temp-DOWNLOADED/new additions/"

------------------------------------------------------------------------
-- Rows by concrete file format.

canonicalDownloadedPdfRows :
  List DownloadedArtifactRow
canonicalDownloadedPdfRows =
  mkDownloadedArtifactRow
    pdfArtifact
    visualizationContext
    "temp-DOWNLOADED/new additions/3D voxel shape mismatch.pdf"
    "3D voxel mismatch context for future supervoxel/Hodge diagnostics"
  ∷ mkDownloadedArtifactRow
    pdfArtifact
    hodgeGRContext
    "temp-DOWNLOADED/new additions/Branch · Formalism Bridging GR and MDL - LES.pdf"
    "formalism bridge context for GR/MDL/Hodge routing"
  ∷ mkDownloadedArtifactRow
    pdfArtifact
    hodgeGRContext
    "temp-DOWNLOADED/new additions/Branch · Formalism Bridging GR and MDL - LES2.pdf"
    "second formalism bridge context for GR/MDL/Hodge routing"
  ∷ mkDownloadedArtifactRow
    pdfArtifact
    quantumSMChemistryContext
    "temp-DOWNLOADED/new additions/Branch · Math Mysticism Breakdown.pdf"
    "claim-discipline context for speculative mathematics wording"
  ∷ mkDownloadedArtifactRow
    pdfArtifact
    quantumSMChemistryContext
    "temp-DOWNLOADED/new additions/DASHI - Dashi on Quantum Computing.pdf"
    "quantum-computing context for finite quantum scope routing"
  ∷ mkDownloadedArtifactRow
    pdfArtifact
    quantumSMChemistryContext
    "temp-DOWNLOADED/new additions/DASHI - Physics - Branch · Outreach Draft Rewrite.pdf"
    "physics outreach context for claim-surface wording"
  ∷ mkDownloadedArtifactRow
    pdfArtifact
    quantumSMChemistryContext
    "temp-DOWNLOADED/new additions/DASHI - Physics - Dark sector physics portals.pdf"
    "dark-sector portal context for SM/frontier routing"
  ∷ mkDownloadedArtifactRow
    pdfArtifact
    quantumSMChemistryContext
    "temp-DOWNLOADED/new additions/DASHI - Physics - Physics Closure in DASHI.pdf"
    "physics-closure context for unification lane routing"
  ∷ mkDownloadedArtifactRow
    pdfArtifact
    quantumSMChemistryContext
    "temp-DOWNLOADED/new additions/DASHI - η′-Mesic Nucleus Discovery.pdf"
    "eta-prime mesic nucleus context for nuclear/empirical intake"
  ∷ mkDownloadedArtifactRow
    pdfArtifact
    quantumSMChemistryContext
    "temp-DOWNLOADED/new additions/Path C model update.pdf"
    "Path C model context for SM/Higgs observable routing"
  ∷ mkDownloadedArtifactRow
    pdfArtifact
    quantumSMChemistryContext
    "temp-DOWNLOADED/new additions/Quantum field count.pdf"
    "quantum field count context for finite/infinite scope boundaries"
  ∷ []

canonicalDownloadedImageRows :
  List DownloadedArtifactRow
canonicalDownloadedImageRows =
  mkDownloadedArtifactRow
    imageArtifact
    visualizationContext
    "temp-DOWNLOADED/new additions/41558_2025_2398_Fig1_HTML.png"
    "external figure intake for visual/context reference"
  ∷ mkDownloadedArtifactRow
    imageArtifact
    constantsAndMeasurementContext
    "temp-DOWNLOADED/new additions/Merrell-Thermometer-wBuffer.webp"
    "measurement illustration intake for constants/calibration context"
  ∷ mkDownloadedArtifactRow
    imageArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/sprint73_eriksson_suppression.png"
    "YM sprint 73 Eriksson suppression plot"
  ∷ mkDownloadedArtifactRow
    imageArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/sprint73_kp_threshold.png"
    "YM sprint 73 KP threshold plot"
  ∷ mkDownloadedArtifactRow
    imageArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/sprint73_proof_ladder.png"
    "YM sprint 73 proof ladder plot"
  ∷ mkDownloadedArtifactRow
    imageArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/ym_67c_route_b.png"
    "YM sprint 67c route B plot"
  ∷ mkDownloadedArtifactRow
    imageArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/ym_67c_two_routes.png"
    "YM sprint 67c two-routes plot"
  ∷ mkDownloadedArtifactRow
    imageArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/ym_sprint67c_obstruction.png"
    "YM sprint 67c obstruction plot"
  ∷ mkDownloadedArtifactRow
    imageArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/ym_sprint70_leakage_paths.png"
    "YM sprint 70 leakage paths plot"
  ∷ mkDownloadedArtifactRow
    imageArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/ym_sprint70_leakage_scenarios.png"
    "YM sprint 70 leakage scenarios plot"
  ∷ mkDownloadedArtifactRow
    imageArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/ym_sprint82_eta_kp_threshold.png"
    "YM sprint 82 eta/KP threshold plot"
  ∷ mkDownloadedArtifactRow
    imageArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/ym_sprint82_qhp_oscillation_decay.png"
    "YM sprint 82 QHP oscillation-decay plot"
  ∷ []

canonicalDownloadedDataRows :
  List DownloadedArtifactRow
canonicalDownloadedDataRows =
  mkDownloadedArtifactRow
    dataArtifact
    constantsAndMeasurementContext
    "temp-DOWNLOADED/new additions/sprint69_constants_table.csv"
    "constants table intake for measured/reference-value routing"
  ∷ mkDownloadedArtifactRow
    dataArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/sprint73_lemma_stack.csv"
    "YM sprint 73 lemma-stack data"
  ∷ mkDownloadedArtifactRow
    dataArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/ym_slab_geometry.csv"
    "YM slab geometry data"
  ∷ mkDownloadedArtifactRow
    dataArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/ym_spatial_slab_entropy_count.csv"
    "YM spatial slab entropy-count data"
  ∷ mkDownloadedArtifactRow
    dataArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/ym_sprint82_assumption_a_oscillation.csv"
    "YM sprint 82 assumption-A oscillation data"
  ∷ mkDownloadedArtifactRow
    dataArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/ym_sprint82_eta_thresholds.csv"
    "YM sprint 82 eta-threshold data"
  ∷ mkDownloadedArtifactRow
    dataArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/ym_sprint82_summary.json"
    "YM sprint 82 summary JSON"
  ∷ mkDownloadedArtifactRow
    dataArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/ym_sprint93_rows.json"
    "YM sprint 93 row JSON"
  ∷ mkDownloadedArtifactRow
    dataArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/ym_sprint93_summary.json"
    "YM sprint 93 summary JSON"
  ∷ mkDownloadedArtifactRow
    dataArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/ym_temporal_support_noncreation_table.csv"
    "YM temporal-support noncreation data"
  ∷ []

canonicalDownloadedCodeRows :
  List DownloadedArtifactRow
canonicalDownloadedCodeRows =
  mkDownloadedArtifactRow
    codeArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/YMSprint93ContinuumGapAttempt.agda"
    "YM sprint 93 formal Agda attempt intake"
  ∷ mkDownloadedArtifactRow
    codeArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/ym_sprint93_master_wc3_calcs.py"
    "YM sprint 93 WC3 calculation script intake"
  ∷ []

canonicalDownloadedHtmlRows :
  List DownloadedArtifactRow
canonicalDownloadedHtmlRows =
  mkDownloadedArtifactRow
    htmlArtifact
    ymClaySprintContext
    "temp-DOWNLOADED/new additions/sprint80-clay-ym-proof-plan.html"
    "YM sprint 80 Clay proof-plan HTML intake"
  ∷ []

canonicalDownloadedArtifactRows :
  List DownloadedArtifactRow
canonicalDownloadedArtifactRows =
  canonicalDownloadedPdfRows
  ++ canonicalDownloadedImageRows
  ++ canonicalDownloadedDataRows
  ++ canonicalDownloadedCodeRows
  ++ canonicalDownloadedHtmlRows

downloadedPdfCount :
  Nat
downloadedPdfCount =
  listCount canonicalDownloadedPdfRows

downloadedImageCount :
  Nat
downloadedImageCount =
  listCount canonicalDownloadedImageRows

downloadedDataCount :
  Nat
downloadedDataCount =
  listCount canonicalDownloadedDataRows

downloadedCodeCount :
  Nat
downloadedCodeCount =
  listCount canonicalDownloadedCodeRows

downloadedHtmlCount :
  Nat
downloadedHtmlCount =
  listCount canonicalDownloadedHtmlRows

downloadedTotalCount :
  Nat
downloadedTotalCount =
  listCount canonicalDownloadedArtifactRows

downloadedPdfCountIs11 :
  downloadedPdfCount ≡ 11
downloadedPdfCountIs11 = refl

downloadedImageCountIs12 :
  downloadedImageCount ≡ 12
downloadedImageCountIs12 = refl

downloadedDataCountIs10 :
  downloadedDataCount ≡ 10
downloadedDataCountIs10 = refl

downloadedCodeCountIs2 :
  downloadedCodeCount ≡ 2
downloadedCodeCountIs2 = refl

downloadedHtmlCountIs1 :
  downloadedHtmlCount ≡ 1
downloadedHtmlCountIs1 = refl

downloadedTotalCountIs36 :
  downloadedTotalCount ≡ 36
downloadedTotalCountIs36 = refl

------------------------------------------------------------------------
-- Emitted reference-index artifacts.

data ReferenceIndexArtifactKind : Set where
  referenceIndexJSON :
    ReferenceIndexArtifactKind

  referenceIndexMarkdown :
    ReferenceIndexArtifactKind

referenceIndexArtifactLabel :
  ReferenceIndexArtifactKind →
  String
referenceIndexArtifactLabel referenceIndexJSON =
  "downloaded new-additions reference index JSON"
referenceIndexArtifactLabel referenceIndexMarkdown =
  "downloaded new-additions reference index Markdown"

record ReferenceIndexArtifactRow : Set where
  field
    referenceArtifactKind :
      ReferenceIndexArtifactKind

    referenceArtifactKindText :
      String

    referenceArtifactKindTextIsCanonical :
      referenceArtifactKindText ≡
        referenceIndexArtifactLabel referenceArtifactKind

    referenceArtifactPath :
      String

    promotesTheorem :
      Bool

    promotesTheoremIsFalse :
      promotesTheorem ≡ false

    promotesEmpiricalValidation :
      Bool

    promotesEmpiricalValidationIsFalse :
      promotesEmpiricalValidation ≡ false

open ReferenceIndexArtifactRow public

mkReferenceIndexArtifactRow :
  ReferenceIndexArtifactKind →
  String →
  ReferenceIndexArtifactRow
mkReferenceIndexArtifactRow kind path =
  record
    { referenceArtifactKind = kind
    ; referenceArtifactKindText = referenceIndexArtifactLabel kind
    ; referenceArtifactKindTextIsCanonical = refl
    ; referenceArtifactPath = path
    ; promotesTheorem = false
    ; promotesTheoremIsFalse = refl
    ; promotesEmpiricalValidation = false
    ; promotesEmpiricalValidationIsFalse = refl
    }

canonicalReferenceIndexArtifactRows :
  List ReferenceIndexArtifactRow
canonicalReferenceIndexArtifactRows =
  mkReferenceIndexArtifactRow
    referenceIndexJSON
    "outputs/downloaded_new_additions_reference_index/downloaded_new_additions_reference_index.json"
  ∷ mkReferenceIndexArtifactRow
    referenceIndexMarkdown
    "outputs/downloaded_new_additions_reference_index/downloaded_new_additions_reference_index.md"
  ∷ []

referenceIndexArtifactCount :
  Nat
referenceIndexArtifactCount =
  listCount canonicalReferenceIndexArtifactRows

referenceIndexArtifactCountIs2 :
  referenceIndexArtifactCount ≡ 2
referenceIndexArtifactCountIs2 = refl

------------------------------------------------------------------------
-- Canonical non-promoting receipt.

record DownloadedNewAdditionsReferenceIndex : Setω where
  field
    receiptLabel :
      String

    sourceRoot :
      String

    artifactRows :
      List DownloadedArtifactRow

    artifactCount :
      Nat

    artifactCountMatches :
      artifactCount ≡ listCount artifactRows

    pdfCount :
      Nat

    pdfCountMatches :
      pdfCount ≡ listCount canonicalDownloadedPdfRows

    imageCount :
      Nat

    imageCountMatches :
      imageCount ≡ listCount canonicalDownloadedImageRows

    dataCount :
      Nat

    dataCountMatches :
      dataCount ≡ listCount canonicalDownloadedDataRows

    codeCount :
      Nat

    codeCountMatches :
      codeCount ≡ listCount canonicalDownloadedCodeRows

    htmlCount :
      Nat

    htmlCountMatches :
      htmlCount ≡ listCount canonicalDownloadedHtmlRows

    referenceIndexArtifacts :
      List ReferenceIndexArtifactRow

    referenceIndexArtifactTotal :
      Nat

    referenceIndexArtifactTotalMatches :
      referenceIndexArtifactTotal ≡
        listCount referenceIndexArtifacts

    theoremAuthority :
      Bool

    theoremAuthorityIsFalse :
      theoremAuthority ≡ false

    empiricalAuthority :
      Bool

    empiricalAuthorityIsFalse :
      empiricalAuthority ≡ false

    promotionAccepted :
      Bool

    promotionAcceptedIsFalse :
      promotionAccepted ≡ false

open DownloadedNewAdditionsReferenceIndex public

canonicalDownloadedNewAdditionsReferenceIndex :
  DownloadedNewAdditionsReferenceIndex
canonicalDownloadedNewAdditionsReferenceIndex =
  record
    { receiptLabel =
        "canonical downloaded new-additions reference index"
    ; sourceRoot =
        basePath
    ; artifactRows =
        canonicalDownloadedArtifactRows
    ; artifactCount =
        downloadedTotalCount
    ; artifactCountMatches =
        refl
    ; pdfCount =
        downloadedPdfCount
    ; pdfCountMatches =
        refl
    ; imageCount =
        downloadedImageCount
    ; imageCountMatches =
        refl
    ; dataCount =
        downloadedDataCount
    ; dataCountMatches =
        refl
    ; codeCount =
        downloadedCodeCount
    ; codeCountMatches =
        refl
    ; htmlCount =
        downloadedHtmlCount
    ; htmlCountMatches =
        refl
    ; referenceIndexArtifacts =
        canonicalReferenceIndexArtifactRows
    ; referenceIndexArtifactTotal =
        referenceIndexArtifactCount
    ; referenceIndexArtifactTotalMatches =
        refl
    ; theoremAuthority =
        false
    ; theoremAuthorityIsFalse =
        refl
    ; empiricalAuthority =
        false
    ; empiricalAuthorityIsFalse =
        refl
    ; promotionAccepted =
        false
    ; promotionAcceptedIsFalse =
        refl
    }

canonicalDownloadedNewAdditionsTotalCountIs36 :
  DownloadedNewAdditionsReferenceIndex.artifactCount
    canonicalDownloadedNewAdditionsReferenceIndex
  ≡ 36
canonicalDownloadedNewAdditionsTotalCountIs36 = refl

canonicalDownloadedNewAdditionsPdfCountIs11 :
  DownloadedNewAdditionsReferenceIndex.pdfCount
    canonicalDownloadedNewAdditionsReferenceIndex
  ≡ 11
canonicalDownloadedNewAdditionsPdfCountIs11 = refl

canonicalDownloadedNewAdditionsImageCountIs12 :
  DownloadedNewAdditionsReferenceIndex.imageCount
    canonicalDownloadedNewAdditionsReferenceIndex
  ≡ 12
canonicalDownloadedNewAdditionsImageCountIs12 = refl

canonicalDownloadedNewAdditionsDataCountIs10 :
  DownloadedNewAdditionsReferenceIndex.dataCount
    canonicalDownloadedNewAdditionsReferenceIndex
  ≡ 10
canonicalDownloadedNewAdditionsDataCountIs10 = refl

canonicalDownloadedNewAdditionsCodeCountIs2 :
  DownloadedNewAdditionsReferenceIndex.codeCount
    canonicalDownloadedNewAdditionsReferenceIndex
  ≡ 2
canonicalDownloadedNewAdditionsCodeCountIs2 = refl

canonicalDownloadedNewAdditionsHtmlCountIs1 :
  DownloadedNewAdditionsReferenceIndex.htmlCount
    canonicalDownloadedNewAdditionsReferenceIndex
  ≡ 1
canonicalDownloadedNewAdditionsHtmlCountIs1 = refl

canonicalDownloadedNewAdditionsReferenceIndexArtifactCountIs2 :
  DownloadedNewAdditionsReferenceIndex.referenceIndexArtifactTotal
    canonicalDownloadedNewAdditionsReferenceIndex
  ≡ 2
canonicalDownloadedNewAdditionsReferenceIndexArtifactCountIs2 = refl
