module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseGuardedCalibrationAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseAttributedSparseTransitionKernelExact as Kernel
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseSupportingMaterialManifestationExact as Manifestation

------------------------------------------------------------------------
-- MANIFESTATION-GUARDED CALIBRATION ACQUISITION
--
-- The current AdK transition kernel is already structurally/source attributed.
-- Numeric upgrading is a separate operation.  This owner binds any future
-- calibration upgrade to the source-manifestation identity guard discovered in
-- the supporting-material lane.
--
-- A value may move from Sparse.unpaidNumeric to Sparse.paidNumeric only after:
--   1. the source manifestation is paid as the same AdK article/supplement;
--   2. an exact locator-specific receipt identifies the state/edge/value;
--   3. the acquisition method is admissible for the claimed value role.
--
-- Neither a foreign legacy PII target nor unreceipted visual/OCR-style guessing
-- can satisfy this gate.
------------------------------------------------------------------------

currentSparseKernel : Kernel.AttributedSparseTransitionKernel
currentSparseKernel = Kernel.canonicalAttributedSparseTransitionKernel

manifestationBoundary : Manifestation.SupportingMaterialManifestationBoundary
manifestationBoundary = Manifestation.canonicalSupportingMaterialManifestationBoundary

data CalibrationPromotionMethod : Set where
  exactMachineReadableSupplementValue : CalibrationPromotionMethod
  exactMachineReadableArticleValue : CalibrationPromotionMethod
  separatelyReceiptedFigureValue : CalibrationPromotionMethod
  unreceiptedVisualTranscription : CalibrationPromotionMethod
  foreignLegacySupplementValue : CalibrationPromotionMethod

record CalibrationPromotionReceipt : Set where
  constructor calibration-promotion-receipt
  field
    targetCell : String
    sourceManifestation : Manifestation.SupportingMaterialManifestation
    method : CalibrationPromotionMethod
    sameObjectManifestationPaid : Bool
    locatorSpecificReceiptPaid : Bool
    valueRolePaid : Bool
    promotionAllowed : Bool
    interpretation : String
open CalibrationPromotionReceipt public

legacyForeignPromotionAttempt : CalibrationPromotionReceipt
legacyForeignPromotionAttempt = calibration-promotion-receipt
  "any AdK sparse numeric cell"
  Manifestation.legacyFootnoteManifestation
  foreignLegacySupplementValue
  false false false false
  "blocked: the legacy supplemental PII resolves to a different article and cannot pay AdK calibration"

figureFiveUnreceiptedAttempt : CalibrationPromotionReceipt
figureFiveUnreceiptedAttempt = calibration-promotion-receipt
  "Figure-5 state energy or Kramers edge-rate label"
  Manifestation.adkArticleManifestation
  unreceiptedVisualTranscription
  true false true false
  "blocked: Figure 5 and its units are source-paid, but an unreceipted visual/OCR-style transcription does not pay a numeric cell"

pmcSupplementCandidate : CalibrationPromotionReceipt
pmcSupplementCandidate = calibration-promotion-receipt
  "future Figure-5/Table-S calibration cell"
  Manifestation.pmcDocumentS1Manifestation
  exactMachineReadableSupplementValue
  true false false false
  "candidate only: the PMC-attached supplement is same-article, but exact locator/value payment has not yet been acquired"

record PaidCalibrationUpgrade : Set where
  constructor paid-calibration-upgrade
  field
    receipt : CalibrationPromotionReceipt
    sameObjectPaid : Bool
    locatorPaid : Bool
    valueRolePaid : Bool
    promotionPaid : Bool
    allPaymentsRequired : Bool
open PaidCalibrationUpgrade public

------------------------------------------------------------------------
-- WrongType / fail-closed firewalls.
------------------------------------------------------------------------

data SameArticleSupplementCreatesEveryNumericCell : Set where
data FigureCaptionCreatesArrowNumeral : Set where
data ForeignPiiCanRepairAdkCalibration : Set where
data MissingLocatorMayBeFilledByVisualGuess : Set where

sameArticleSupplementDoesNotCreateEveryNumericCell :
  SameArticleSupplementCreatesEveryNumericCell → ⊥
sameArticleSupplementDoesNotCreateEveryNumericCell ()

figureCaptionDoesNotCreateArrowNumeral : FigureCaptionCreatesArrowNumeral → ⊥
figureCaptionDoesNotCreateArrowNumeral ()

foreignPiiCannotRepairAdkCalibration : ForeignPiiCanRepairAdkCalibration → ⊥
foreignPiiCannotRepairAdkCalibration ()

missingLocatorCannotBeFilledByVisualGuess : MissingLocatorMayBeFilledByVisualGuess → ⊥
missingLocatorCannotBeFilledByVisualGuess ()

------------------------------------------------------------------------
-- Frontier.
------------------------------------------------------------------------

record GuardedCalibrationAcquisitionBoundary : Set where
  constructor guarded-calibration-acquisition-boundary
  field
    sparseKernelRetained : Bool
    manifestationGuardRetained : Bool
    sameObjectSupplementCandidateRetained : Bool
    locatorSpecificReceiptRequired : Bool
    machineReadableAcquisitionPreferred : Bool
    exactFigureFiveRateNumericsPaid : Bool
    exactPerStateFigureFiveEnergyNumericsPaid : Bool
    namedStateDLnNumericsPaid : Bool
    legacyForeignSupplementMayPay : Bool
    unreceiptedVisualReadoutMayPay : Bool
    kramersRateMayPromoteToExperimentalRate : Bool
    nextResidual : String
open GuardedCalibrationAcquisitionBoundary public

canonicalGuardedCalibrationAcquisitionBoundary : GuardedCalibrationAcquisitionBoundary
canonicalGuardedCalibrationAcquisitionBoundary = guarded-calibration-acquisition-boundary
  true true true true true
  false false false false false false
  "acquire a same-article machine-readable Document-S1/S2 value or a separately receipted Figure-5 readout with exact state/edge locator. Only then upgrade the corresponding sparse cell; preserve Kramers-derived rate kind and relative-free-energy reference semantics, and keep the legacy foreign PII collision as provenance."
