module DASHI.Physics.Closure.BothwellYe2022MillimetreRedshiftReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.QuantumClockProperTimeRedshiftBridge as Redshift
import DASHI.Physics.Closure.QuantumClockDimensionlessObservableLaw as Dimensionless
import DASHI.Physics.Closure.QuantumClockEmpiricalRedshiftReceiptRequest as Request

------------------------------------------------------------------------
-- Bothwell et al. (Nature 602, 420–424, 2022) empirical-contact bridge.
--
-- The existing repository already owns the symbolic law surfaces
--
--   Delta f / f = Delta U / c^2
--   Delta tau / Delta t = g h / c^2
--   Delta phi = omega0 * Delta tau
--
-- and separately requires an empirical redshift receipt.
--
-- This module records the 2022 JILA/NIST strontium result as a sourced
-- experiment descriptor attached to those owners.  It deliberately keeps
-- three claims distinct:
--
--   (1) the law shape is internal repository mathematics;
--   (2) the experiment reports a linear frequency gradient consistent with
--       gravitational redshift within one millimetre-scale ultracold
--       strontium sample;
--   (3) that consistency is empirical contact, not a formal proof of GR and
--       not a replacement for the repository's stronger checksum/raw-data/
--       systematics ingestion gate.
--
-- Source:
-- Tobias Bothwell et al., "Resolving the gravitational redshift across a
-- millimetre-scale atomic sample", Nature 602, 420–424 (2022),
-- DOI 10.1038/s41586-021-04349-7, published 16 February 2022.

data MillimetreRedshiftEvidenceStatus : Set where
  sourceVerifiedPartialReceipt :
    MillimetreRedshiftEvidenceStatus

record BothwellYe2022Source : Set where
  field
    title :
      String

    journalCitation :
      String

    doi :
      String

    publicationDate :
      String

    leadAuthor :
      String

    correspondingAuthor :
      String

    sourceUri :
      String

open BothwellYe2022Source public

canonicalBothwellYe2022Source : BothwellYe2022Source
canonicalBothwellYe2022Source =
  record
    { title =
        "Resolving the gravitational redshift across a millimetre-scale atomic sample"
    ; journalCitation =
        "Nature 602, 420-424 (2022)"
    ; doi =
        "10.1038/s41586-021-04349-7"
    ; publicationDate =
        "2022-02-16"
    ; leadAuthor =
        "Tobias Bothwell"
    ; correspondingAuthor =
        "Jun Ye"
    ; sourceUri =
        "https://www.nature.com/articles/s41586-021-04349-7"
    }

record BothwellYe2022ExperimentSurface : Set where
  field
    species :
      String

    sampleScale :
      String

    confinement :
      String

    observedQuantity :
      String

    reportedFinding :
      String

    fractionalFrequencyUncertainty :
      String

    directionReading :
      String

    internalLawReference :
      String

    requestReference :
      String

open BothwellYe2022ExperimentSurface public

canonicalBothwellYe2022ExperimentSurface : BothwellYe2022ExperimentSurface
canonicalBothwellYe2022ExperimentSurface =
  record
    { species =
        "ultracold strontium"
    ; sampleScale =
        "single millimetre-scale sample"
    ; confinement =
        "vertically oriented optical lattice"
    ; observedQuantity =
        "spatially resolved optical-clock frequency gradient"
    ; reportedFinding =
        "linear frequency gradient consistent with gravitational redshift"
    ; fractionalFrequencyUncertainty =
        "7.6e-21"
    ; directionReading =
        "higher gravitational potential corresponds to the faster clock in the leading weak-field redshift law"
    ; internalLawReference =
        "DASHI.Physics.Closure.QuantumClockProperTimeRedshiftBridge.leadingUniformFieldRedshiftBoundaryLabel"
    ; requestReference =
        "DASHI.Physics.Closure.QuantumClockEmpiricalRedshiftReceiptRequest.opticalClockHeightComparisonRequested"
    }

record EquationToMeasurementContact : Set where
  field
    symbolicLaw :
      String

    symbolicOwner :
      String

    apparatusMap :
      String

    measurableObservable :
      String

    reportedContact :
      String

    equationAndMeasurementSeparated :
      Bool

    equationAndMeasurementSeparatedIsTrue :
      equationAndMeasurementSeparated ≡ true

open EquationToMeasurementContact public

canonicalEquationToMeasurementContact : EquationToMeasurementContact
canonicalEquationToMeasurementContact =
  record
    { symbolicLaw =
        "Delta f / f = Delta U / c^2; locally Delta U = g h"
    ; symbolicOwner =
        "DASHI.Physics.Closure.QuantumClockProperTimeRedshiftBridge"
    ; apparatusMap =
        "vertical position in one ultracold strontium cloud -> local gravitational-potential difference -> resolved clock-frequency bin"
    ; measurableObservable =
        "frequency gradient across the atomic sample"
    ; reportedContact =
        "Bothwell et al. report a linear gradient consistent with the gravitational redshift prediction"
    ; equationAndMeasurementSeparated =
        true
    ; equationAndMeasurementSeparatedIsTrue =
        refl
    }

record ExistingMachineryAttachment : Set where
  field
    properTimeBridge :
      Redshift.QuantumClockProperTimeRedshiftBridge

    properTimeBridgeIsCanonical :
      properTimeBridge ≡ Redshift.canonicalQuantumClockProperTimeRedshiftBridge

    dimensionlessLaw :
      Dimensionless.QuantumClockDimensionlessObservableLaw

    dimensionlessLawIsCanonical :
      dimensionlessLaw ≡ Dimensionless.canonicalQuantumClockDimensionlessObservableLaw

    empiricalRequest :
      Request.QuantumClockEmpiricalRedshiftReceiptRequest

    empiricalRequestIsCanonical :
      empiricalRequest ≡ Request.canonicalQuantumClockEmpiricalRedshiftReceiptRequest

open ExistingMachineryAttachment public

canonicalExistingMachineryAttachment : ExistingMachineryAttachment
canonicalExistingMachineryAttachment =
  record
    { properTimeBridge =
        Redshift.canonicalQuantumClockProperTimeRedshiftBridge
    ; properTimeBridgeIsCanonical =
        refl
    ; dimensionlessLaw =
        Dimensionless.canonicalQuantumClockDimensionlessObservableLaw
    ; dimensionlessLawIsCanonical =
        refl
    ; empiricalRequest =
        Request.canonicalQuantumClockEmpiricalRedshiftReceiptRequest
    ; empiricalRequestIsCanonical =
        refl
    }

record BothwellYe2022ReceiptBoundary : Set where
  field
    source :
      BothwellYe2022Source

    sourceIsCanonical :
      source ≡ canonicalBothwellYe2022Source

    experiment :
      BothwellYe2022ExperimentSurface

    experimentIsCanonical :
      experiment ≡ canonicalBothwellYe2022ExperimentSurface

    contact :
      EquationToMeasurementContact

    contactIsCanonical :
      contact ≡ canonicalEquationToMeasurementContact

    attachment :
      ExistingMachineryAttachment

    attachmentIsCanonical :
      attachment ≡ canonicalExistingMachineryAttachment

    sourceMetadataRecorded :
      Bool

    sourceMetadataRecordedIsTrue :
      sourceMetadataRecorded ≡ true

    abstractLevelMeasurementRecorded :
      Bool

    abstractLevelMeasurementRecordedIsTrue :
      abstractLevelMeasurementRecorded ≡ true

    exactMillimetreCarrierClaimed :
      Bool

    exactMillimetreCarrierClaimedIsFalse :
      exactMillimetreCarrierClaimed ≡ false

    rawDataIngested :
      Bool

    rawDataIngestedIsFalse :
      rawDataIngested ≡ false

    sourceSha256Recorded :
      Bool

    sourceSha256RecordedIsFalse :
      sourceSha256Recorded ≡ false

    fullSystematicsReceiptAccepted :
      Bool

    fullSystematicsReceiptAcceptedIsFalse :
      fullSystematicsReceiptAccepted ≡ false

    empiricalConsistencyPromotedToProofOfGR :
      Bool

    empiricalConsistencyPromotedToProofOfGRIsFalse :
      empiricalConsistencyPromotedToProofOfGR ≡ false

    requestFullyDischarged :
      Bool

    requestFullyDischargedIsFalse :
      requestFullyDischarged ≡ false

    evidenceStatus :
      MillimetreRedshiftEvidenceStatus

    reading :
      List String

open BothwellYe2022ReceiptBoundary public

canonicalBothwellYe2022ReceiptBoundary : BothwellYe2022ReceiptBoundary
canonicalBothwellYe2022ReceiptBoundary =
  record
    { source =
        canonicalBothwellYe2022Source
    ; sourceIsCanonical =
        refl
    ; experiment =
        canonicalBothwellYe2022ExperimentSurface
    ; experimentIsCanonical =
        refl
    ; contact =
        canonicalEquationToMeasurementContact
    ; contactIsCanonical =
        refl
    ; attachment =
        canonicalExistingMachineryAttachment
    ; attachmentIsCanonical =
        refl
    ; sourceMetadataRecorded =
        true
    ; sourceMetadataRecordedIsTrue =
        refl
    ; abstractLevelMeasurementRecorded =
        true
    ; abstractLevelMeasurementRecordedIsTrue =
        refl
    ; exactMillimetreCarrierClaimed =
        false
    ; exactMillimetreCarrierClaimedIsFalse =
        refl
    ; rawDataIngested =
        false
    ; rawDataIngestedIsFalse =
        refl
    ; sourceSha256Recorded =
        false
    ; sourceSha256RecordedIsFalse =
        refl
    ; fullSystematicsReceiptAccepted =
        false
    ; fullSystematicsReceiptAcceptedIsFalse =
        refl
    ; empiricalConsistencyPromotedToProofOfGR =
        false
    ; empiricalConsistencyPromotedToProofOfGRIsFalse =
        refl
    ; requestFullyDischarged =
        false
    ; requestFullyDischargedIsFalse =
        refl
    ; evidenceStatus =
        sourceVerifiedPartialReceipt
    ; reading =
        "The repository law surface supplies the equation; the Nature experiment supplies a measured spatial frequency-gradient contact point."
        ∷ "The source says millimetre-scale; this module intentionally does not silently strengthen that wording to an exact 1 mm carrier."
        ∷ "The reported 7.6e-21 fractional frequency uncertainty is recorded as source text, not converted here into a new exact numeric theorem."
        ∷ "A source-level consistency result is not promoted to a proof of general relativity."
        ∷ "The stronger repository receipt still awaits checksum/raw-data/systematics/covariance/SI-binding ingestion before terminal promotion."
        ∷ []
    }

canonicalBothwellYe2022DoesNotOverclaimExactOneMillimetre :
  exactMillimetreCarrierClaimed canonicalBothwellYe2022ReceiptBoundary ≡ false
canonicalBothwellYe2022DoesNotOverclaimExactOneMillimetre =
  refl

canonicalBothwellYe2022DoesNotPromoteConsistencyToGRProof :
  empiricalConsistencyPromotedToProofOfGR canonicalBothwellYe2022ReceiptBoundary ≡ false
canonicalBothwellYe2022DoesNotPromoteConsistencyToGRProof =
  refl

canonicalBothwellYe2022LeavesFullReceiptOpen :
  requestFullyDischarged canonicalBothwellYe2022ReceiptBoundary ≡ false
canonicalBothwellYe2022LeavesFullReceiptOpen =
  refl
