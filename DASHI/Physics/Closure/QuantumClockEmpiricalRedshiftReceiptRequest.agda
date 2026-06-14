module DASHI.Physics.Closure.QuantumClockEmpiricalRedshiftReceiptRequest where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.QuantumClockDimensionlessObservableLaw as Dimensionless
import DASHI.Physics.Closure.QuantumClockProperTimeRedshiftBridge as Redshift

------------------------------------------------------------------------
-- Quantum-clock empirical redshift receipt request.
--
-- The dimensionless law surface only checks that Delta U / c^2 has no SI
-- base dimension.  This module records the separate empirical-contact
-- request: an external experiment must supply artifact provenance, raw
-- measurement text, uncertainty, apparatus/systematics, covariance or
-- independence treatment, SI-unit binding, and consumer ingestion.  No
-- experiment is accepted or promoted here.

data ⊥ : Set where

data EmpiricalRedshiftExperimentKind : Set where
  gpsClockComparison :
    EmpiricalRedshiftExperimentKind

  poundRebkaGammaRedshift :
    EmpiricalRedshiftExperimentKind

  gravityProbeAHydrogenMaser :
    EmpiricalRedshiftExperimentKind

  opticalClockHeightComparison :
    EmpiricalRedshiftExperimentKind

  atomInterferometerClockComparison :
    EmpiricalRedshiftExperimentKind

record EmpiricalRedshiftExperimentDescriptor : Set where
  field
    experimentKind :
      EmpiricalRedshiftExperimentKind

    experimentLabel :
      String

    observableLawShape :
      String

    empiricalContactRole :
      String

    internalLawOnly :
      Bool

    internalLawOnlyIsTrue :
      internalLawOnly ≡ true

    empiricalReceiptAccepted :
      Bool

    empiricalReceiptAcceptedIsFalse :
      empiricalReceiptAccepted ≡ false

open EmpiricalRedshiftExperimentDescriptor public

mkRequestedExperiment :
  EmpiricalRedshiftExperimentKind →
  String →
  String →
  EmpiricalRedshiftExperimentDescriptor
mkRequestedExperiment kind label role =
  record
    { experimentKind =
        kind
    ; experimentLabel =
        label
    ; observableLawShape =
        "Delta f / f = Delta U / c^2, equivalently Delta phi = omega0 * Delta tau after SI-second binding"
    ; empiricalContactRole =
        role
    ; internalLawOnly =
        true
    ; internalLawOnlyIsTrue =
        refl
    ; empiricalReceiptAccepted =
        false
    ; empiricalReceiptAcceptedIsFalse =
        refl
    }

gpsClockComparisonRequested :
  EmpiricalRedshiftExperimentDescriptor
gpsClockComparisonRequested =
  mkRequestedExperiment
    gpsClockComparison
    "GPS satellite/ground clock gravitational-redshift comparison"
    "operational clock-comparison contact point for fractional frequency shift after orbital, special-relativistic, and systematics modelling"

poundRebkaRequested :
  EmpiricalRedshiftExperimentDescriptor
poundRebkaRequested =
  mkRequestedExperiment
    poundRebkaGammaRedshift
    "Pound-Rebka gravitational redshift"
    "laboratory height-potential contact point using resonant gamma-ray frequency shift"

gravityProbeARequested :
  EmpiricalRedshiftExperimentDescriptor
gravityProbeARequested =
  mkRequestedExperiment
    gravityProbeAHydrogenMaser
    "Gravity Probe A hydrogen maser redshift"
    "spaceborne clock contact point comparing elapsed proper time against a ground reference"

opticalClockHeightComparisonRequested :
  EmpiricalRedshiftExperimentDescriptor
opticalClockHeightComparisonRequested =
  mkRequestedExperiment
    opticalClockHeightComparison
    "optical-clock height comparison"
    "modern laboratory clock contact point resolving gravitational potential differences through optical frequency ratios"

atomInterferometerClockComparisonRequested :
  EmpiricalRedshiftExperimentDescriptor
atomInterferometerClockComparisonRequested =
  mkRequestedExperiment
    atomInterferometerClockComparison
    "atom-interferometer clock comparison"
    "phase-readout contact point for Delta phi = omega0 * Delta tau with apparatus-specific coherence and recoil modelling"

canonicalRequestedExperimentKinds :
  List EmpiricalRedshiftExperimentDescriptor
canonicalRequestedExperimentKinds =
  gpsClockComparisonRequested
  ∷ poundRebkaRequested
  ∷ gravityProbeARequested
  ∷ opticalClockHeightComparisonRequested
  ∷ atomInterferometerClockComparisonRequested
  ∷ []

data EmpiricalRedshiftEvidenceField : Set where
  sourceArtifactField :
    EmpiricalRedshiftEvidenceField

  sourceArtifactSha256Field :
    EmpiricalRedshiftEvidenceField

  sourceAccessDateField :
    EmpiricalRedshiftEvidenceField

  rawMeasurementField :
    EmpiricalRedshiftEvidenceField

  rawUncertaintyField :
    EmpiricalRedshiftEvidenceField

  apparatusDescriptionField :
    EmpiricalRedshiftEvidenceField

  systematicsBudgetField :
    EmpiricalRedshiftEvidenceField

  covarianceOrIndependenceField :
    EmpiricalRedshiftEvidenceField

  siUnitBindingField :
    EmpiricalRedshiftEvidenceField

  gravitationalPotentialModelField :
    EmpiricalRedshiftEvidenceField

  consumerIngestionReceiptField :
    EmpiricalRedshiftEvidenceField

data EmpiricalRedshiftEvidenceStatus : Set where
  requiredExternalEvidence :
    EmpiricalRedshiftEvidenceStatus

record EmpiricalRedshiftEvidenceRow : Set where
  field
    evidenceField :
      EmpiricalRedshiftEvidenceField

    evidenceName :
      String

    requiredContent :
      String

    gatesOnto :
      String

    evidenceStatus :
      EmpiricalRedshiftEvidenceStatus

    evidenceAccepted :
      Bool

    evidenceAcceptedIsFalse :
      evidenceAccepted ≡ false

open EmpiricalRedshiftEvidenceRow public

mkEvidenceRow :
  EmpiricalRedshiftEvidenceField →
  String →
  String →
  String →
  EmpiricalRedshiftEvidenceRow
mkEvidenceRow key name content gate =
  record
    { evidenceField =
        key
    ; evidenceName =
        name
    ; requiredContent =
        content
    ; gatesOnto =
        gate
    ; evidenceStatus =
        requiredExternalEvidence
    ; evidenceAccepted =
        false
    ; evidenceAcceptedIsFalse =
        refl
    }

sourceArtifactEvidenceRow :
  EmpiricalRedshiftEvidenceRow
sourceArtifactEvidenceRow =
  mkEvidenceRow
    sourceArtifactField
    "sourceArtifact"
    "stable experiment publication, standards report, mission data product, or laboratory comparison artifact identity"
    "EmpiricalQuantumClockRedshiftReceipt.sourceArtifact"

sourceArtifactSha256EvidenceRow :
  EmpiricalRedshiftEvidenceRow
sourceArtifactSha256EvidenceRow =
  mkEvidenceRow
    sourceArtifactSha256Field
    "sourceArtifactSha256"
    "SHA256 digest or equivalent immutable checksum for the cited artifact"
    "EmpiricalQuantumClockRedshiftReceipt.sourceArtifactSha256"

sourceAccessDateEvidenceRow :
  EmpiricalRedshiftEvidenceRow
sourceAccessDateEvidenceRow =
  mkEvidenceRow
    sourceAccessDateField
    "sourceAccessDate"
    "ISO-8601 access date for the external artifact or data product"
    "EmpiricalQuantumClockRedshiftReceipt.sourceAccessDate"

rawMeasurementEvidenceRow :
  EmpiricalRedshiftEvidenceRow
rawMeasurementEvidenceRow =
  mkEvidenceRow
    rawMeasurementField
    "rawMeasurement"
    "verbatim fractional redshift, frequency-ratio, phase-shift, or fitted Delta f / f value from the source"
    "NumericQuantumClockPayload.rawMeasurement"

rawUncertaintyEvidenceRow :
  EmpiricalRedshiftEvidenceRow
rawUncertaintyEvidenceRow =
  mkEvidenceRow
    rawUncertaintyField
    "rawUncertainty"
    "verbatim statistical and systematic uncertainty text, including confidence convention"
    "NumericQuantumClockPayload.rawUncertainty"

apparatusDescriptionEvidenceRow :
  EmpiricalRedshiftEvidenceRow
apparatusDescriptionEvidenceRow =
  mkEvidenceRow
    apparatusDescriptionField
    "apparatusDescription"
    "clock species, transition/frequency reference, geometry, height or orbit, comparison link, and measurement interval"
    "EmpiricalQuantumClockRedshiftReceipt.apparatusDescription"

systematicsBudgetEvidenceRow :
  EmpiricalRedshiftEvidenceRow
systematicsBudgetEvidenceRow =
  mkEvidenceRow
    systematicsBudgetField
    "systematicsBudget"
    "redshift corrections, Doppler/Sagnac terms, environmental shifts, calibration chain, and residual systematics"
    "EmpiricalQuantumClockRedshiftReceipt.systematicsBudget"

covarianceOrIndependenceEvidenceRow :
  EmpiricalRedshiftEvidenceRow
covarianceOrIndependenceEvidenceRow =
  mkEvidenceRow
    covarianceOrIndependenceField
    "covarianceOrIndependence"
    "covariance matrix for fitted terms, or an independence receipt justifying scalar uncertainty combination"
    "EmpiricalQuantumClockRedshiftReceipt.covarianceOrIndependence"

siUnitBindingEvidenceRow :
  EmpiricalRedshiftEvidenceRow
siUnitBindingEvidenceRow =
  mkEvidenceRow
    siUnitBindingField
    "siUnitBinding"
    "binding from reported seconds, hertz, metres, potential, or phase units onto the atomic-clock SI carrier"
    "Candidate256PhysicalCalibrationExternalReceipt.physicalUnitCarrier"

gravitationalPotentialModelEvidenceRow :
  EmpiricalRedshiftEvidenceRow
gravitationalPotentialModelEvidenceRow =
  mkEvidenceRow
    gravitationalPotentialModelField
    "gravitationalPotentialModel"
    "model for Delta U or height-to-potential conversion used by the cited experiment"
    "QuantumClockProperTimeRedshiftBridge.uniform-field or mission-specific potential model"

consumerIngestionReceiptEvidenceRow :
  EmpiricalRedshiftEvidenceRow
consumerIngestionReceiptEvidenceRow =
  mkEvidenceRow
    consumerIngestionReceiptField
    "consumerIngestionReceipt"
    "DASHI ingestion receipt linking parsed experiment payload to the clock-redshift promotion surface"
    "DimensionlessObservablePromotionToken.consumerIngestionReceipt"

canonicalRequiredEvidenceRows :
  List EmpiricalRedshiftEvidenceRow
canonicalRequiredEvidenceRows =
  sourceArtifactEvidenceRow
  ∷ sourceArtifactSha256EvidenceRow
  ∷ sourceAccessDateEvidenceRow
  ∷ rawMeasurementEvidenceRow
  ∷ rawUncertaintyEvidenceRow
  ∷ apparatusDescriptionEvidenceRow
  ∷ systematicsBudgetEvidenceRow
  ∷ covarianceOrIndependenceEvidenceRow
  ∷ siUnitBindingEvidenceRow
  ∷ gravitationalPotentialModelEvidenceRow
  ∷ consumerIngestionReceiptEvidenceRow
  ∷ []

data EmpiricalRedshiftReceiptAcceptanceToken : Set where

data EmpiricalRedshiftPromotionToken : Set where

empiricalRedshiftReceiptAcceptanceTokenUnavailableHere :
  EmpiricalRedshiftReceiptAcceptanceToken →
  ⊥
empiricalRedshiftReceiptAcceptanceTokenUnavailableHere ()

empiricalRedshiftPromotionTokenUnavailableHere :
  EmpiricalRedshiftPromotionToken →
  ⊥
empiricalRedshiftPromotionTokenUnavailableHere ()

record EmpiricalRedshiftFailClosedGuards : Set where
  field
    anyExperimentIngested :
      Bool

    anyExperimentIngestedIsFalse :
      anyExperimentIngested ≡ false

    anyEvidenceAccepted :
      Bool

    anyEvidenceAcceptedIsFalse :
      anyEvidenceAccepted ≡ false

    receiptAccepted :
      Bool

    receiptAcceptedIsFalse :
      receiptAccepted ≡ false

    promotionTokenConstructed :
      Bool

    promotionTokenConstructedIsFalse :
      promotionTokenConstructed ≡ false

    lawShapeAlreadyInternal :
      Bool

    lawShapeAlreadyInternalIsTrue :
      lawShapeAlreadyInternal ≡ true

    empiricalContactStillExternal :
      Bool

    empiricalContactStillExternalIsTrue :
      empiricalContactStillExternal ≡ true

open EmpiricalRedshiftFailClosedGuards public

canonicalEmpiricalRedshiftFailClosedGuards :
  EmpiricalRedshiftFailClosedGuards
canonicalEmpiricalRedshiftFailClosedGuards =
  record
    { anyExperimentIngested =
        false
    ; anyExperimentIngestedIsFalse =
        refl
    ; anyEvidenceAccepted =
        false
    ; anyEvidenceAcceptedIsFalse =
        refl
    ; receiptAccepted =
        false
    ; receiptAcceptedIsFalse =
        refl
    ; promotionTokenConstructed =
        false
    ; promotionTokenConstructedIsFalse =
        refl
    ; lawShapeAlreadyInternal =
        true
    ; lawShapeAlreadyInternalIsTrue =
        refl
    ; empiricalContactStillExternal =
        true
    ; empiricalContactStillExternalIsTrue =
        refl
    }

record QuantumClockEmpiricalRedshiftReceiptRequest : Setω where
  field
    dimensionlessLawSurface :
      Dimensionless.QuantumClockDimensionlessObservableLaw

    dimensionlessLawSurfaceImportedFromCanonicalSurface :
      Bool

    dimensionlessLawSurfaceImportedFromCanonicalSurfaceIsTrue :
      dimensionlessLawSurfaceImportedFromCanonicalSurface ≡ true

    properTimeRedshiftBridge :
      Redshift.QuantumClockProperTimeRedshiftBridge

    properTimeRedshiftBridgeImportedFromCanonicalSurface :
      Bool

    properTimeRedshiftBridgeImportedFromCanonicalSurfaceIsTrue :
      properTimeRedshiftBridgeImportedFromCanonicalSurface ≡ true

    requestedExperiments :
      List EmpiricalRedshiftExperimentDescriptor

    requestedExperimentsAreCanonical :
      requestedExperiments ≡ canonicalRequestedExperimentKinds

    requiredEvidenceRows :
      List EmpiricalRedshiftEvidenceRow

    requiredEvidenceRowsAreCanonical :
      requiredEvidenceRows ≡ canonicalRequiredEvidenceRows

    failClosedGuards :
      EmpiricalRedshiftFailClosedGuards

    failClosedGuardsAreCanonical :
      failClosedGuards ≡ canonicalEmpiricalRedshiftFailClosedGuards

    noAcceptanceToken :
      EmpiricalRedshiftReceiptAcceptanceToken →
      ⊥

    noPromotionToken :
      EmpiricalRedshiftPromotionToken →
      ⊥

    lawShapeVsEmpiricalContactReading :
      List String

open QuantumClockEmpiricalRedshiftReceiptRequest public

canonicalQuantumClockEmpiricalRedshiftReceiptRequest :
  QuantumClockEmpiricalRedshiftReceiptRequest
canonicalQuantumClockEmpiricalRedshiftReceiptRequest =
  record
    { dimensionlessLawSurface =
        Dimensionless.canonicalQuantumClockDimensionlessObservableLaw
    ; dimensionlessLawSurfaceImportedFromCanonicalSurface =
        true
    ; dimensionlessLawSurfaceImportedFromCanonicalSurfaceIsTrue =
        refl
    ; properTimeRedshiftBridge =
        Redshift.canonicalQuantumClockProperTimeRedshiftBridge
    ; properTimeRedshiftBridgeImportedFromCanonicalSurface =
        true
    ; properTimeRedshiftBridgeImportedFromCanonicalSurfaceIsTrue =
        refl
    ; requestedExperiments =
        canonicalRequestedExperimentKinds
    ; requestedExperimentsAreCanonical =
        refl
    ; requiredEvidenceRows =
        canonicalRequiredEvidenceRows
    ; requiredEvidenceRowsAreCanonical =
        refl
    ; failClosedGuards =
        canonicalEmpiricalRedshiftFailClosedGuards
    ; failClosedGuardsAreCanonical =
        refl
    ; noAcceptanceToken =
        empiricalRedshiftReceiptAcceptanceTokenUnavailableHere
    ; noPromotionToken =
        empiricalRedshiftPromotionTokenUnavailableHere
    ; lawShapeVsEmpiricalContactReading =
        "DimensionlessObservableLaw supplies only the law-shape proof that Delta U / c^2 is dimensionless."
        ∷ "QuantumClockProperTimeRedshiftBridge supplies the leading redshift law surface, not an experiment."
        ∷ "Empirical contact requires an external experiment row: GPS, Pound-Rebka, Gravity Probe A, optical-clock height comparison, or atom-interferometer clock comparison."
        ∷ "Each experiment row needs artifact identity, checksum, access date, raw measurement, uncertainty, apparatus/systematics, covariance or independence, SI-unit binding, gravitational-potential model, and ingestion receipt."
        ∷ "No experiment is ingested, no evidence is accepted, and no empirical redshift receipt or promotion token is constructed here."
        ∷ []
    }

canonicalEmpiricalRedshiftNoExperimentIngested :
  anyExperimentIngested
    (failClosedGuards canonicalQuantumClockEmpiricalRedshiftReceiptRequest)
  ≡
  false
canonicalEmpiricalRedshiftNoExperimentIngested =
  refl

canonicalEmpiricalRedshiftNoEvidenceAccepted :
  anyEvidenceAccepted
    (failClosedGuards canonicalQuantumClockEmpiricalRedshiftReceiptRequest)
  ≡
  false
canonicalEmpiricalRedshiftNoEvidenceAccepted =
  refl

canonicalEmpiricalRedshiftReceiptNotAccepted :
  receiptAccepted
    (failClosedGuards canonicalQuantumClockEmpiricalRedshiftReceiptRequest)
  ≡
  false
canonicalEmpiricalRedshiftReceiptNotAccepted =
  refl

canonicalEmpiricalRedshiftPromotionNotConstructed :
  promotionTokenConstructed
    (failClosedGuards canonicalQuantumClockEmpiricalRedshiftReceiptRequest)
  ≡
  false
canonicalEmpiricalRedshiftPromotionNotConstructed =
  refl

canonicalEmpiricalRedshiftLawShapeInternal :
  lawShapeAlreadyInternal
    (failClosedGuards canonicalQuantumClockEmpiricalRedshiftReceiptRequest)
  ≡
  true
canonicalEmpiricalRedshiftLawShapeInternal =
  refl

canonicalEmpiricalRedshiftContactStillExternal :
  empiricalContactStillExternal
    (failClosedGuards canonicalQuantumClockEmpiricalRedshiftReceiptRequest)
  ≡
  true
canonicalEmpiricalRedshiftContactStillExternal =
  refl
