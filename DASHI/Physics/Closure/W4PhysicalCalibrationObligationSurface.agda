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

data W4PhysicalCalibrationFirstMissingPrerequisite : Set where
  missingSameRecordT21T22ArtifactReceipt :
    W4PhysicalCalibrationFirstMissingPrerequisite
  missingT43RunnerGeneralizationForZPeakAnchor :
    W4PhysicalCalibrationFirstMissingPrerequisite
  missingSharedPDFBackedZPeakShapeAdequacy :
    W4PhysicalCalibrationFirstMissingPrerequisite
  missingDirtyZPeakShapeAdequacy :
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
  missingSharedPDFBackedZPeakShapeAdequacy
  ∷ missingDirtyZPeakShapeAdequacy
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

    crossBandWitnessPrerequisite :
      String

    externalCalibrationPrerequisite :
      String

    firstMissingPrerequisites :
      List W4PhysicalCalibrationFirstMissingPrerequisite

    nextPrerequisite :
      W4PhysicalCalibrationFirstMissingPrerequisite

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

    nonPromotionBoundary :
      List String

    zPeakCalibrationLawImpossibleHere :
      ZPeak.W4SameRecordZPeakRatioCalibrationLaw →
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
    ; crossBandWitnessPrerequisite =
        "consume Candidate256 quotient/cross-band witness only through strict physical scale-setting fields, not as physical calibration authority"
    ; externalCalibrationPrerequisite =
        "provide Candidate256PhysicalCalibrationExternalReceipt with authority token, units, calibration map, quotient-scale factorization, and dimensional preservation"
    ; firstMissingPrerequisites =
        canonicalW4PhysicalCalibrationFirstMissingPrerequisites
    ; nextPrerequisite =
        missingSharedPDFBackedZPeakShapeAdequacy
    ; strictPhysicalNextMissingIngredient =
        Ledger.candidate256RecommendedNextMissingIngredient
    ; postPDFAuthorityMatterFirstMissingChain =
        missingSharedPDFBackedZPeakShapeAdequacy
        ∷ missingExternalPhysicalCalibrationReceipt
        ∷ missingMatterFieldFromW4
        ∷ missingStressEnergyTensorFromW4
        ∷ []
    ; grMatterSourceQueue =
        "First supply the shared CT18/MSHT/LHAPDF-compatible parton-luminosity intake that makes the W4 Z-peak shape adequate"
        ∷ "Then supply Candidate256PhysicalCalibrationExternalReceipt with authority token, physical unit carrier, calibration map, quotient-scale factorization, and dimensional preservation"
        ∷ "Only after that receipt exists, construct matterFieldFromW4 from the calibrated W4 physical unit carrier and Candidate256 quotient-scale map"
        ∷ "Then construct stressEnergyTensorFromW4 over that matter field for the GR Einstein-equation lane"
        ∷ []
    ; exactNextObligationMapping =
        "Z-peak data/cache is present: t21 measurement and t22 covariance local artifacts from HEPData record ins2079374 are digest-bound"
        ∷ "Shared PDF prerequisite: W4 dirty Z-peak shape adequacy and W5 t45 correction both wait on missingSharedCT18MSHTLHAPDFPartonLuminosityIntake"
        ∷ "Runner blocker moved: dirty-z-peak accepts a declared uncalibrated shape callable plus one scalar fit, but current shape chi2/dof is 298.8462841768543"
        ∷ "Cross-band prerequisite: Candidate256 quotient/cross-band witness is available but remains pre-scale-setting"
        ∷ "Physical calibration prerequisite: external Candidate256 receipt must supply authority, unit carrier, calibration, factorization, and dimensional preservation"
        ∷ "Matter-source prerequisite: matterFieldFromW4 and stressEnergyTensorFromW4 are downstream of the external physical calibration receipt, not current W4 evidence"
        ∷ "Strict physical lane: recommended next chemistry-facing lane is scale setting, before spectra, bonding, and empirical validation"
        ∷ []
    ; matterSourceBoundary =
        "This W4 surface only names the matter-source queue required by GR"
        ∷ "It does not construct matterFieldFromW4"
        ∷ "It does not construct stressEnergyTensorFromW4"
        ∷ "It does not construct a sourced non-flat connection or an Einstein-equation receipt"
        ∷ "Those constructions remain inadmissible until PDF-backed W4 adequacy and Candidate256PhysicalCalibrationExternalReceipt exist"
        ∷ []
    ; nonPromotionBoundary =
        "This surface only maps already-existing W4 request, route, Z-peak, and chemistry-ledger obligations"
        ∷ "It does not construct W4SameRecordZPeakRatioCalibrationLaw"
        ∷ "It does not construct Candidate256PhysicalCalibrationExternalReceipt"
        ∷ "It does not construct matterFieldFromW4 or stressEnergyTensorFromW4"
        ∷ "It does not construct physical unit authority, dimensional preservation, scale-setting closure, spectra, bonding, empirical validation, or W4 promotion"
        ∷ []
    ; zPeakCalibrationLawImpossibleHere =
        ZPeak.canonicalW4CalibrationRatioZPeakLawIsUninhabited
    ; externalReceiptImpossibleHere =
        External.candidate256PhysicalCalibrationExternalReceiptImpossibleHere
    }

canonicalW4PhysicalCalibrationNextPrerequisite :
  W4PhysicalCalibrationFirstMissingPrerequisite
canonicalW4PhysicalCalibrationNextPrerequisite =
  W4PhysicalCalibrationObligationSurface.nextPrerequisite
    canonicalW4PhysicalCalibrationObligationSurface
