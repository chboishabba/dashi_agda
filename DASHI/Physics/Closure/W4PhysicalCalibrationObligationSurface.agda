module DASHI.Physics.Closure.W4PhysicalCalibrationObligationSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCandidate256Witness as Candidate256
import DASHI.Physics.Closure.ChemistryRightLimitsQuotientCrossBandCouplingRequirement as CrossBand
import DASHI.Physics.Closure.ChemistryStrictPhysicalSemanticsBlocker as Blocker
import DASHI.Physics.Closure.W4CalibrationRatioZPeakReceiptRequestSurface as ZPeak
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptObligation as External
import DASHI.Physics.Closure.W4PhysicalCalibrationExternalReceiptRequestPack as Request
import DASHI.Physics.Closure.W4PhysicalCalibrationRouteNarrowing as Route
import DASHI.Physics.Closure.W4StrictPhysicalObligationLedger as Ledger
import DASHI.Physics.Closure.W4W5AcceptedDYLuminosityConventionDiagnostic as DY
import DASHI.Physics.Closure.W4W5PDFSharedDependencyDiagnostic as SharedPDF

------------------------------------------------------------------------
-- W4 physical-calibration first-missing obligation surface.
--
-- This is only a diagnostic aggregation of existing W4 surfaces.  It names
-- the same-record Z-peak artifact anchor, the Candidate256 quotient/cross-band
-- witness prerequisite, and the external calibration receipt still required
-- before any physical scale-setting or promotion can be consumed.

data W4PhysicalCalibrationObligationSurfaceStatus : Set where
  blockedAtZPeakArtifactAndCrossBandPrerequisitesOnly :
    W4PhysicalCalibrationObligationSurfaceStatus

data AcceptedDYLuminosityConvention : Set where

acceptedDYLuminosityConventionImpossibleHere :
  AcceptedDYLuminosityConvention →
  ⊥
acceptedDYLuminosityConventionImpossibleHere ()

data AcceptedDYLuminosityConventionAuthorityBoundary : Set where

acceptedDYLuminosityConventionAuthorityBoundaryImpossibleHere :
  AcceptedDYLuminosityConventionAuthorityBoundary →
  ⊥
acceptedDYLuminosityConventionAuthorityBoundaryImpossibleHere ()

data W4PhysicalCalibrationReceiptQueueItem : Set where
  AcceptedDYLuminosityConventionAuthority :
    W4PhysicalCalibrationReceiptQueueItem
  W4ZAdequacy :
    W4PhysicalCalibrationReceiptQueueItem
  Candidate256PhysicalCalibrationExternalReceipt :
    W4PhysicalCalibrationReceiptQueueItem

canonicalW4PhysicalCalibrationReceiptQueue :
  List W4PhysicalCalibrationReceiptQueueItem
canonicalW4PhysicalCalibrationReceiptQueue =
  AcceptedDYLuminosityConventionAuthority
  ∷ W4ZAdequacy
  ∷ Candidate256PhysicalCalibrationExternalReceipt
  ∷ []

data W4PhysicalCalibrationFirstMissingPrerequisite : Set where
  missingAcceptedDYLuminosityConventionAuthority :
    W4PhysicalCalibrationFirstMissingPrerequisite
  missingAcceptedDYLuminosityConvention :
    W4PhysicalCalibrationFirstMissingPrerequisite
  missingSameRecordT21T22ArtifactReceipt :
    W4PhysicalCalibrationFirstMissingPrerequisite
  missingT43RunnerGeneralizationForZPeakAnchor :
    W4PhysicalCalibrationFirstMissingPrerequisite
  missingSharedPDFBackedZPeakShapeAdequacy :
    W4PhysicalCalibrationFirstMissingPrerequisite
  missingDirtyZPeakShapeAdequacy :
    W4PhysicalCalibrationFirstMissingPrerequisite
  missingW4ZAdequacy :
    W4PhysicalCalibrationFirstMissingPrerequisite
  missingExternalPhysicalCalibrationReceipt :
    W4PhysicalCalibrationFirstMissingPrerequisite
  missingMatterFieldFromW4 :
    W4PhysicalCalibrationFirstMissingPrerequisite
  missingStressEnergyTensorFromW4 :
    W4PhysicalCalibrationFirstMissingPrerequisite
  missingStrictPhysicalScaleSettingConsumer :
    W4PhysicalCalibrationFirstMissingPrerequisite

canonicalW4PhysicalCalibrationFirstMissingPrerequisites :
  List W4PhysicalCalibrationFirstMissingPrerequisite
canonicalW4PhysicalCalibrationFirstMissingPrerequisites =
  missingAcceptedDYLuminosityConventionAuthority
  ∷ missingW4ZAdequacy
  ∷ missingExternalPhysicalCalibrationReceipt
  ∷ missingMatterFieldFromW4
  ∷ missingStressEnergyTensorFromW4
  ∷ missingStrictPhysicalScaleSettingConsumer
  ∷ []

record W4PhysicalCalibrationObligationSurface : Setω where
  field
    status :
      W4PhysicalCalibrationObligationSurfaceStatus

    zPeakRequestSurface :
      ZPeak.W4CalibrationRatioZPeakReceiptRequestSurface

    externalReceiptRequestPack :
      Request.W4PhysicalCalibrationExternalReceiptRequestPack

    routeNarrowingStatus :
      Route.W4PhysicalCalibrationRouteNarrowingCurrentStatus

    strictPhysicalLedger :
      Ledger.Candidate256StrictPhysicalAllNeededLedger

    candidate256CrossBandLaw :
      CrossBand.ChemistryRightLimitsQuotientCrossBandLaw

    candidate256StrictNextLane :
      Ledger.Candidate256StrictPhysicalLane

    zPeakAnchorName :
      String

    zPeakT21T22ArtifactRequest :
      ZPeak.W4SameRecordZPeakT21T22ArtifactReceiptRequest

    zPeakDirtyBoundaryDiagnostic :
      ZPeak.W4ZPeakDirtyBoundaryCheckSupportDiagnostic

    sharedPDFDependency :
      SharedPDF.W4W5PDFSharedDependencyDiagnostic

    acceptedDYLuminosityConventionName :
      String

    acceptedDYLuminosityConventionBoundary :
      List String

    acceptedDYLuminosityConventionAuthorityFirstMissing :
      DY.W4W5DYLuminosityFirstMissing

    receiptQueue :
      List W4PhysicalCalibrationReceiptQueueItem

    receiptQueueName :
      String

    crossBandWitnessPrerequisite :
      String

    externalCalibrationPrerequisite :
      String

    legitimateExternalReceiptBoundary :
      List String

    firstMissingPrerequisites :
      List W4PhysicalCalibrationFirstMissingPrerequisite

    nextPrerequisite :
      W4PhysicalCalibrationFirstMissingPrerequisite

    exactFirstMissingStatus :
      String

    strictPhysicalNextMissingIngredient :
      Blocker.StrictPhysicalMissingIngredient

    postPDFAuthorityMatterFirstMissingChain :
      List W4PhysicalCalibrationFirstMissingPrerequisite

    grMatterSourceQueue :
      List String

    exactNextObligationMapping :
      List String

    matterSourceBoundary :
      List String

    limitedSMGRPaperBoundary :
      List String

    nonPromotionBoundary :
      List String

    zPeakCalibrationLawImpossibleHere :
      ZPeak.W4SameRecordZPeakRatioCalibrationLaw →
      ⊥

    acceptedDYLuminosityConventionBoundaryImpossibleHere :
      AcceptedDYLuminosityConvention →
      ⊥

    acceptedDYLuminosityConventionAuthorityImpossibleHere :
      AcceptedDYLuminosityConventionAuthorityBoundary →
      ⊥

    externalReceiptImpossibleHere :
      External.Candidate256PhysicalCalibrationExternalReceipt →
      ⊥

canonicalW4PhysicalCalibrationObligationSurface :
  W4PhysicalCalibrationObligationSurface
canonicalW4PhysicalCalibrationObligationSurface =
  record
    { status =
        blockedAtZPeakArtifactAndCrossBandPrerequisitesOnly
    ; zPeakRequestSurface =
        ZPeak.canonicalW4CalibrationRatioZPeakReceiptRequestSurface
    ; externalReceiptRequestPack =
        Request.canonicalW4PhysicalCalibrationExternalReceiptRequestPack
    ; routeNarrowingStatus =
        Route.canonicalW4PhysicalCalibrationRouteNarrowingCurrentStatus
    ; strictPhysicalLedger =
        Ledger.canonicalCandidate256StrictPhysicalAllNeededLedger
    ; candidate256CrossBandLaw =
        Candidate256.canonicalCandidate256QuotientCrossBandLaw
    ; candidate256StrictNextLane =
        Ledger.candidate256RecommendedNextLane
    ; zPeakAnchorName =
        "same-record CMS/HEPData Z-peak phistar ratio-calibration anchor"
    ; zPeakT21T22ArtifactRequest =
        ZPeak.canonicalW4SameRecordZPeakT21T22ArtifactReceiptRequest
    ; zPeakDirtyBoundaryDiagnostic =
        ZPeak.canonicalW4ZPeakDirtyBoundaryCheckSupportDiagnostic
    ; sharedPDFDependency =
        SharedPDF.canonicalW4W5PDFSharedDependencyDiagnostic
    ; acceptedDYLuminosityConventionName =
        "AcceptedDYLuminosityConventionAuthority"
    ; acceptedDYLuminosityConventionBoundary =
        "Constructorless W4-local convention boundary: an accepted Drell-Yan parton-luminosity/bin-integration convention must be supplied before PDF-backed W4 adequacy can feed matterFieldFromW4"
        ∷ "The convention must bind PDF family/member, grid checksums, x/Q2 or rapidity-window integration, flavour weights, normalization, covariance treatment, and W4/W5 pass/fail tolerances"
        ∷ "The current local CT18 probes are diagnostics only; they do not inhabit AcceptedDYLuminosityConventionAuthority"
        ∷ []
    ; acceptedDYLuminosityConventionAuthorityFirstMissing =
        DY.missingAcceptedDYLuminosityConventionAuthority
    ; receiptQueue =
        canonicalW4PhysicalCalibrationReceiptQueue
    ; receiptQueueName =
        "AcceptedDYLuminosityConventionAuthority -> W4ZAdequacy -> Candidate256PhysicalCalibrationExternalReceipt"
    ; crossBandWitnessPrerequisite =
        "consume Candidate256 quotient/cross-band witness only through strict physical scale-setting fields, not as physical calibration authority"
    ; externalCalibrationPrerequisite =
        "provide Candidate256PhysicalCalibrationExternalReceipt with authority token, units, calibration map, quotient-scale factorization, and dimensional preservation"
    ; legitimateExternalReceiptBoundary =
        External.Candidate256PhysicalCalibrationExternalReceiptCurrentStatus.legitimateAuthorityArtifactBoundary
          External.canonicalCandidate256PhysicalCalibrationExternalReceiptCurrentStatus
    ; firstMissingPrerequisites =
        canonicalW4PhysicalCalibrationFirstMissingPrerequisites
    ; nextPrerequisite =
        missingAcceptedDYLuminosityConventionAuthority
    ; exactFirstMissingStatus =
        "first missing now: missingAcceptedDYLuminosityConventionAuthority; queue: AcceptedDYLuminosityConventionAuthority -> W4ZAdequacy -> Candidate256PhysicalCalibrationExternalReceipt"
    ; strictPhysicalNextMissingIngredient =
        Ledger.candidate256RecommendedNextMissingIngredient
    ; postPDFAuthorityMatterFirstMissingChain =
        missingAcceptedDYLuminosityConventionAuthority
        ∷ missingW4ZAdequacy
        ∷ missingExternalPhysicalCalibrationReceipt
        ∷ missingMatterFieldFromW4
        ∷ missingStressEnergyTensorFromW4
        ∷ []
    ; grMatterSourceQueue =
        "First supply AcceptedDYLuminosityConventionAuthority over the shared CT18/MSHT/LHAPDF-compatible parton-luminosity intake"
        ∷ "Then establish W4ZAdequacy from that accepted convention authority"
        ∷ "Then supply Candidate256PhysicalCalibrationExternalReceipt with authority token, physical unit carrier, calibration map, quotient-scale factorization, and dimensional preservation"
        ∷ "Only after that receipt exists, construct matterFieldFromW4 from the calibrated W4 physical unit carrier and Candidate256 quotient-scale map"
        ∷ "Then construct stressEnergyTensorFromW4 over that matter field for the GR Einstein-equation lane"
        ∷ []
    ; exactNextObligationMapping =
        "Z-peak data/cache is present: t21 measurement and t22 covariance local artifacts from HEPData record ins2079374 are digest-bound"
        ∷ "Accepted DY luminosity prerequisite: no AcceptedDYLuminosityConventionAuthority is inhabited for the local CT18/MSHT/LHAPDF packet"
        ∷ "W4 adequacy prerequisite: W4ZAdequacy is downstream of accepted DY convention authority, not current local probes"
        ∷ "Runner blocker moved: dirty-z-peak accepts a declared uncalibrated shape callable plus one scalar fit, but current shape chi2/dof is 298.8462841768543"
        ∷ "Cross-band prerequisite: Candidate256 quotient/cross-band witness is available but remains pre-scale-setting"
        ∷ "Physical calibration prerequisite: external Candidate256 receipt must supply authority, unit carrier, calibration, factorization, and dimensional preservation"
        ∷ "Matter-source prerequisite: matterFieldFromW4 and stressEnergyTensorFromW4 are downstream of AcceptedDYLuminosityConventionAuthority, W4ZAdequacy, and Candidate256PhysicalCalibrationExternalReceipt, not current W4 evidence"
        ∷ "Strict physical lane: recommended next chemistry-facing lane is scale setting, before spectra, bonding, and empirical validation"
        ∷ []
    ; matterSourceBoundary =
        "This W4 surface only names the matter-source queue required by GR"
        ∷ "It does not construct matterFieldFromW4"
        ∷ "It does not construct stressEnergyTensorFromW4"
        ∷ "It does not construct a sourced non-flat connection or an Einstein-equation receipt"
        ∷ "Those constructions remain inadmissible until AcceptedDYLuminosityConventionAuthority, W4ZAdequacy, and Candidate256PhysicalCalibrationExternalReceipt exist"
        ∷ []
    ; limitedSMGRPaperBoundary =
        "Limited paper claim: this surface records a typed SM-to-GR matter-source obligation path, not a broad unification theorem"
        ∷ "Current W4 evidence can name Z-peak/PDF/calibration prerequisites but cannot source non-flat GR geometry"
        ∷ "The first missing item is the accepted Drell-Yan luminosity/bin-integration convention; the external physical calibration receipt remains unconstructed"
        ∷ "Candidate256PhysicalCalibrationExternalReceipt is queued after AcceptedDYLuminosityConventionAuthority and W4ZAdequacy, so this surface does not imply Candidate256 calibration is available"
        ∷ "Any later SM+GR bridge must consume actual matterFieldFromW4 and stressEnergyTensorFromW4 terms, not this request surface"
        ∷ []
    ; nonPromotionBoundary =
        "This surface only maps already-existing W4 request, route, Z-peak, and chemistry-ledger obligations"
        ∷ "It does not construct W4SameRecordZPeakRatioCalibrationLaw"
        ∷ "It does not construct AcceptedDYLuminosityConventionAuthority"
        ∷ "It does not construct W4ZAdequacy"
        ∷ "It does not construct Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "It does not construct matterFieldFromW4 or stressEnergyTensorFromW4"
        ∷ "It does not construct physical unit authority, dimensional preservation, scale-setting closure, spectra, bonding, empirical validation, or W4 promotion"
        ∷ []
    ; zPeakCalibrationLawImpossibleHere =
        ZPeak.canonicalW4CalibrationRatioZPeakLawIsUninhabited
    ; acceptedDYLuminosityConventionBoundaryImpossibleHere =
        acceptedDYLuminosityConventionImpossibleHere
    ; acceptedDYLuminosityConventionAuthorityImpossibleHere =
        acceptedDYLuminosityConventionAuthorityBoundaryImpossibleHere
    ; externalReceiptImpossibleHere =
        External.candidate256PhysicalCalibrationExternalReceiptImpossibleHere
    }

canonicalW4PhysicalCalibrationNextPrerequisite :
  W4PhysicalCalibrationFirstMissingPrerequisite
canonicalW4PhysicalCalibrationNextPrerequisite =
  W4PhysicalCalibrationObligationSurface.nextPrerequisite
    canonicalW4PhysicalCalibrationObligationSurface
