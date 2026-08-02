module DASHI.Physics.Closure.NSTriadKNCherevanCompanionScalingAudit where

------------------------------------------------------------------------
-- PROVENANCE
-- Author: Pylyp Cherevan.
-- Title: "A log-free estimate for the diagonal paraproduct high x high to
-- low in the 3D Navier-Stokes equation".
-- Venue/year: arXiv preprint, submitted 9 October 2025.
-- Journal DOI: none recorded.
-- arXiv/DataCite DOI: 10.48550/arXiv.2510.07848.
-- arXiv: 2510.07848v1.
-- Uses: reconnaissance of the stated projection P_{< N^(1-delta)} applied to
-- the diagonal high-high-to-low derivative term.
-- Relationship: cross-checks the companion paper against arXiv:2510.06246,
-- whose narrow-region proof uses lambda^(-delta).  The two conventions are
-- recorded as internally inconsistent until an author correction or complete
-- derivation reconciles them.  Neither paper is consumed as a DASHI theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNCherevanResonantParaproductAudit as Resonant

data FrequencyScalingConvention : Set where
  inversePowerNarrowScale
  dimensionallyRelativeLowScale
  reconciledScalingDerivation : FrequencyScalingConvention

resonantPaperNarrowScaling : FrequencyScalingConvention
resonantPaperNarrowScaling = inversePowerNarrowScale

companionPaperProjectionScaling : FrequencyScalingConvention
companionPaperProjectionScaling = dimensionallyRelativeLowScale

companionSourceExists : Bool
companionSourceExists = true

companionArxivDOIVerified : Bool
companionArxivDOIVerified = true

companionPeerReviewed : Bool
companionPeerReviewed = false

companionSingleResonantComponentOnly : Bool
companionSingleResonantComponentOnly = true

companionUsesNToOneMinusDeltaProjection : Bool
companionUsesNToOneMinusDeltaProjection = true

crossPaperScalingConventionsAgreeAsWritten : Bool
crossPaperScalingConventionsAgreeAsWritten = false

crossPaperScalingReconciledByPublishedCorrection : Bool
crossPaperScalingReconciledByPublishedCorrection = false

companionUsableAsStage3Theorem : Bool
companionUsableAsStage3Theorem = false

record CherevanCrossPaperScalingReceipt : Set where
  constructor receipt
  field
    resonantSourceAlreadyReconnaissanceOnly :
      Resonant.cherevanConsumedAsStage3Theorem ≡ false
    resonantUsesInversePowerConvention :
      resonantPaperNarrowScaling ≡ inversePowerNarrowScale
    companionUsesRelativeLowConvention :
      companionPaperProjectionScaling ≡ dimensionallyRelativeLowScale
    companionSourceReceipt : companionSourceExists ≡ true
    companionDOIReceipt : companionArxivDOIVerified ≡ true
    companionPreprintReceipt : companionPeerReviewed ≡ false
    companionSingleComponentReceipt :
      companionSingleResonantComponentOnly ≡ true
    explicitProjectionReceipt :
      companionUsesNToOneMinusDeltaProjection ≡ true
    conventionsDoNotAgreeReceipt :
      crossPaperScalingConventionsAgreeAsWritten ≡ false
    noPublishedReconciliationReceipt :
      crossPaperScalingReconciledByPublishedCorrection ≡ false
    companionTheoremUseBlockedReceipt :
      companionUsableAsStage3Theorem ≡ false

open CherevanCrossPaperScalingReceipt public

cherevanCrossPaperScalingReceipt : CherevanCrossPaperScalingReceipt
cherevanCrossPaperScalingReceipt =
  receipt
    Resonant.cherevanConsumedAsStage3TheoremIsFalse
    refl refl refl refl refl refl refl refl refl refl

cherevanCrossPaperScalingAuditRepresented : Bool
cherevanCrossPaperScalingAuditRepresented = true

cherevanCrossPaperScalingAuditRepresentedIsTrue :
  cherevanCrossPaperScalingAuditRepresented ≡ true
cherevanCrossPaperScalingAuditRepresentedIsTrue = refl
