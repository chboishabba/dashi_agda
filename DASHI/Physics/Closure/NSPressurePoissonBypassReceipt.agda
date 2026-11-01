module DASHI.Physics.Closure.NSPressurePoissonBypassReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Fail-closed receipt for the pressure-Poisson bypass route.
--
-- This module records the bypass surface only. It keeps the route closed
-- against promotion while noting the analytic shape the user described:
--   * on dOmega_K = {lambda2 = 0}, tr(S^2) = 2*g12^2,
--   * pressure Poisson gives -Delta p = tr(S^2) - |omega|^2 / 4,
--   * hence |omega|^2 <= 4 * (2*g12^2 + |Delta p|),
--   * the surface L2 bound is recorded with area and H5/pressure terms,
--   * Q3 extensional threshold is bypassed, but the route is fail-closed
--     pending layer pressure, CZ, coarea, and geometric concentration.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSPressurePoissonBypassStatus : Set where
  pressurePoissonBypassReceiptRecorded :
    NSPressurePoissonBypassStatus

data NSPressurePoissonBypassStage : Set where
  bypassSurfaceRecorded :
    NSPressurePoissonBypassStage
  lambda2ZeroBoundaryRecorded :
    NSPressurePoissonBypassStage
  traceS2IdentityRecorded :
    NSPressurePoissonBypassStage
  pressurePoissonIdentityRecorded :
    NSPressurePoissonBypassStage
  omegaInequalityRecorded :
    NSPressurePoissonBypassStage
  surfaceL2AreaEstimateRecorded :
    NSPressurePoissonBypassStage
  h5PressureTermRecorded :
    NSPressurePoissonBypassStage
  q3ExtensionalThresholdBypassedRecorded :
    NSPressurePoissonBypassStage
  layerPressurePendingRecorded :
    NSPressurePoissonBypassStage
  czPendingRecorded :
    NSPressurePoissonBypassStage
  coareaPendingRecorded :
    NSPressurePoissonBypassStage
  geometricConcentrationPendingRecorded :
    NSPressurePoissonBypassStage
  noPromotionRecorded :
    NSPressurePoissonBypassStage

canonicalNSPressurePoissonBypassStages :
  List NSPressurePoissonBypassStage
canonicalNSPressurePoissonBypassStages =
  bypassSurfaceRecorded
  ∷ lambda2ZeroBoundaryRecorded
  ∷ traceS2IdentityRecorded
  ∷ pressurePoissonIdentityRecorded
  ∷ omegaInequalityRecorded
  ∷ surfaceL2AreaEstimateRecorded
  ∷ h5PressureTermRecorded
  ∷ q3ExtensionalThresholdBypassedRecorded
  ∷ layerPressurePendingRecorded
  ∷ czPendingRecorded
  ∷ coareaPendingRecorded
  ∷ geometricConcentrationPendingRecorded
  ∷ noPromotionRecorded
  ∷ []

data NSPressurePoissonBypassBlocker : Set where
  layerPressureStillOpen :
    NSPressurePoissonBypassBlocker
  czStillOpen :
    NSPressurePoissonBypassBlocker
  coareaStillOpen :
    NSPressurePoissonBypassBlocker
  geometricConcentrationStillOpen :
    NSPressurePoissonBypassBlocker
  q3ThresholdBypassIsNotPromotion :
    NSPressurePoissonBypassBlocker
  failClosedUntilAnalyticClosure :
    NSPressurePoissonBypassBlocker

canonicalNSPressurePoissonBypassBlockers :
  List NSPressurePoissonBypassBlocker
canonicalNSPressurePoissonBypassBlockers =
  layerPressureStillOpen
  ∷ czStillOpen
  ∷ coareaStillOpen
  ∷ geometricConcentrationStillOpen
  ∷ q3ThresholdBypassIsNotPromotion
  ∷ failClosedUntilAnalyticClosure
  ∷ []

oTextValue : String
oTextValue =
  "On dOmega_K = {lambda2 = 0}, tr(S^2) = 2*g12^2."

rTextValue : String
rTextValue =
  "Pressure Poisson gives -Delta p = tr(S^2) - |omega|^2 / 4."

cTextValue : String
cTextValue =
  "Hence |omega|^2 <= 4 * (2*g12^2 + |Delta p|)."

sTextValue : String
sTextValue =
  "The surface L2 bound is recorded with area and H5/pressure terms."

lTextValue : String
lTextValue =
  "Layer pressure remains pending, so the route stays fail-closed."

pTextValue : String
pTextValue =
  "CZ and coarea remain pending, and the bypass is not promoted."

gTextValue : String
gTextValue =
  "Geometric concentration remains pending as a closure guard."

fTextValue : String
fTextValue =
  "Q3 extensional threshold is bypassed, but promotion remains false."

receiptBoundaryText : List String
receiptBoundaryText =
  "O: on dOmega_K = {lambda2 = 0}, tr(S^2) = 2*g12^2"
  ∷ "R: pressure Poisson records -Delta p = tr(S^2) - |omega|^2 / 4"
  ∷ "C: |omega|^2 <= 4 * (2*g12^2 + |Delta p|)"
  ∷ "S: surface L2 bound is recorded with area and H5/pressure terms"
  ∷ "L: layer pressure remains pending"
  ∷ "P: CZ and coarea remain pending"
  ∷ "G: geometric concentration remains pending"
  ∷ "F: Q3 threshold is bypassed but not promoted"
  ∷ []

canonicalBoundaryText : String
canonicalBoundaryText =
  "Pressure-Poisson bypass receipt: on dOmega_K = {lambda2 = 0}, tr(S^2) = 2*g12^2; pressure Poisson gives -Delta p = tr(S^2) - |omega|^2 / 4; the derived inequality |omega|^2 <= 4 * (2*g12^2 + |Delta p|) is recorded together with the surface L2 area/H5-pressure bound, while Q3 extensional threshold bypass remains fail-closed pending layer pressure, CZ, coarea, and geometric concentration."

data NSPressurePoissonBypassPromotion : Set where

nsPressurePoissonBypassPromotionImpossibleHere :
  NSPressurePoissonBypassPromotion → ⊥
nsPressurePoissonBypassPromotionImpossibleHere ()

record NSPressurePoissonBypassReceipt : Set where
  constructor mkNSPressurePoissonBypassReceipt
  field
    status :
      NSPressurePoissonBypassStatus
    statusIsCanonical :
      status ≡ pressurePoissonBypassReceiptRecorded

    stageTrail :
      List NSPressurePoissonBypassStage
    stageTrailIsCanonical :
      stageTrail ≡ canonicalNSPressurePoissonBypassStages
    stageCount :
      Nat
    stageCountIsCanonical :
      stageCount ≡ listLength canonicalNSPressurePoissonBypassStages

    blockerTrail :
      List NSPressurePoissonBypassBlocker
    blockerTrailIsCanonical :
      blockerTrail ≡ canonicalNSPressurePoissonBypassBlockers
    blockerCount :
      Nat
    blockerCountIsCanonical :
      blockerCount ≡ listLength canonicalNSPressurePoissonBypassBlockers

    oText :
      String
    oTextIsCanonical :
      oText ≡ oTextValue
    rText :
      String
    rTextIsCanonical :
      rText ≡ rTextValue
    cText :
      String
    cTextIsCanonical :
      cText ≡ cTextValue
    sText :
      String
    sTextIsCanonical :
      sText ≡ sTextValue
    lText :
      String
    lTextIsCanonical :
      lText ≡ lTextValue
    pText :
      String
    pTextIsCanonical :
      pText ≡ pTextValue
    gText :
      String
    gTextIsCanonical :
      gText ≡ gTextValue
    fText :
      String
    fTextIsCanonical :
      fText ≡ fTextValue

    lambda2ZeroBoundaryFlag :
      Bool
    lambda2ZeroBoundaryFlagIsTrue :
      lambda2ZeroBoundaryFlag ≡ true

    traceS2IdentityFlag :
      Bool
    traceS2IdentityFlagIsTrue :
      traceS2IdentityFlag ≡ true

    pressurePoissonIdentityFlag :
      Bool
    pressurePoissonIdentityFlagIsTrue :
      pressurePoissonIdentityFlag ≡ true

    omegaInequalityFlag :
      Bool
    omegaInequalityFlagIsTrue :
      omegaInequalityFlag ≡ true

    surfaceL2AreaEstimateFlag :
      Bool
    surfaceL2AreaEstimateFlagIsTrue :
      surfaceL2AreaEstimateFlag ≡ true

    q3ExtensionalThresholdBypassed :
      Bool
    q3ExtensionalThresholdBypassedIsTrue :
      q3ExtensionalThresholdBypassed ≡ true

    layerPressureClosed :
      Bool
    layerPressureClosedIsFalse :
      layerPressureClosed ≡ false

    czClosed :
      Bool
    czClosedIsFalse :
      czClosed ≡ false

    coareaClosed :
      Bool
    coareaClosedIsFalse :
      coareaClosed ≡ false

    geometricConcentrationClosed :
      Bool
    geometricConcentrationClosedIsFalse :
      geometricConcentrationClosed ≡ false

    promotionGranted :
      Bool
    promotionGrantedIsFalse :
      promotionGranted ≡ false

    receiptBoundary :
      List String
    receiptBoundaryIsCanonical :
      receiptBoundary ≡ receiptBoundaryText
    receiptBoundaryParagraph :
      String
    receiptBoundaryParagraphIsCanonical :
      receiptBoundaryParagraph ≡ canonicalBoundaryText

open NSPressurePoissonBypassReceipt public

canonicalNSPressurePoissonBypassReceipt :
  NSPressurePoissonBypassReceipt
canonicalNSPressurePoissonBypassReceipt =
  mkNSPressurePoissonBypassReceipt
    pressurePoissonBypassReceiptRecorded
    refl
    canonicalNSPressurePoissonBypassStages
    refl
    (listLength canonicalNSPressurePoissonBypassStages)
    refl
    canonicalNSPressurePoissonBypassBlockers
    refl
    (listLength canonicalNSPressurePoissonBypassBlockers)
    refl
    oTextValue
    refl
    rTextValue
    refl
    cTextValue
    refl
    sTextValue
    refl
    lTextValue
    refl
    pTextValue
    refl
    gTextValue
    refl
    fTextValue
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    receiptBoundaryText
    refl
    canonicalBoundaryText
    refl

canonicalNSPressurePoissonBypassStatusIsCanonical :
  status canonicalNSPressurePoissonBypassReceipt ≡
  pressurePoissonBypassReceiptRecorded
canonicalNSPressurePoissonBypassStatusIsCanonical = refl

canonicalNSPressurePoissonBypassStageTrailIsCanonical :
  stageTrail canonicalNSPressurePoissonBypassReceipt ≡
  canonicalNSPressurePoissonBypassStages
canonicalNSPressurePoissonBypassStageTrailIsCanonical = refl

canonicalNSPressurePoissonBypassStageCountIsCanonical :
  stageCount canonicalNSPressurePoissonBypassReceipt ≡
  listLength canonicalNSPressurePoissonBypassStages
canonicalNSPressurePoissonBypassStageCountIsCanonical = refl

canonicalNSPressurePoissonBypassBlockerTrailIsCanonical :
  blockerTrail canonicalNSPressurePoissonBypassReceipt ≡
  canonicalNSPressurePoissonBypassBlockers
canonicalNSPressurePoissonBypassBlockerTrailIsCanonical = refl

canonicalNSPressurePoissonBypassBlockerCountIsCanonical :
  blockerCount canonicalNSPressurePoissonBypassReceipt ≡
  listLength canonicalNSPressurePoissonBypassBlockers
canonicalNSPressurePoissonBypassBlockerCountIsCanonical = refl

canonicalNSPressurePoissonBypassOTextIsCanonical :
  oText canonicalNSPressurePoissonBypassReceipt ≡ oTextValue
canonicalNSPressurePoissonBypassOTextIsCanonical = refl

canonicalNSPressurePoissonBypassRTextIsCanonical :
  rText canonicalNSPressurePoissonBypassReceipt ≡ rTextValue
canonicalNSPressurePoissonBypassRTextIsCanonical = refl

canonicalNSPressurePoissonBypassCTextIsCanonical :
  cText canonicalNSPressurePoissonBypassReceipt ≡ cTextValue
canonicalNSPressurePoissonBypassCTextIsCanonical = refl

canonicalNSPressurePoissonBypassSTextIsCanonical :
  sText canonicalNSPressurePoissonBypassReceipt ≡ sTextValue
canonicalNSPressurePoissonBypassSTextIsCanonical = refl

canonicalNSPressurePoissonBypassLTextIsCanonical :
  lText canonicalNSPressurePoissonBypassReceipt ≡ lTextValue
canonicalNSPressurePoissonBypassLTextIsCanonical = refl

canonicalNSPressurePoissonBypassPTextIsCanonical :
  pText canonicalNSPressurePoissonBypassReceipt ≡ pTextValue
canonicalNSPressurePoissonBypassPTextIsCanonical = refl

canonicalNSPressurePoissonBypassGTextIsCanonical :
  gText canonicalNSPressurePoissonBypassReceipt ≡ gTextValue
canonicalNSPressurePoissonBypassGTextIsCanonical = refl

canonicalNSPressurePoissonBypassFTextIsCanonical :
  fText canonicalNSPressurePoissonBypassReceipt ≡ fTextValue
canonicalNSPressurePoissonBypassFTextIsCanonical = refl

canonicalNSPressurePoissonBypassQ3ThresholdBypassedIsTrue :
  q3ExtensionalThresholdBypassed canonicalNSPressurePoissonBypassReceipt ≡ true
canonicalNSPressurePoissonBypassQ3ThresholdBypassedIsTrue = refl

canonicalNSPressurePoissonBypassLayerPressureClosedIsFalse :
  layerPressureClosed canonicalNSPressurePoissonBypassReceipt ≡ false
canonicalNSPressurePoissonBypassLayerPressureClosedIsFalse = refl

canonicalNSPressurePoissonBypassCZClosedIsFalse :
  czClosed canonicalNSPressurePoissonBypassReceipt ≡ false
canonicalNSPressurePoissonBypassCZClosedIsFalse = refl

canonicalNSPressurePoissonBypassCoareaClosedIsFalse :
  coareaClosed canonicalNSPressurePoissonBypassReceipt ≡ false
canonicalNSPressurePoissonBypassCoareaClosedIsFalse = refl

canonicalNSPressurePoissonBypassGeometricConcentrationClosedIsFalse :
  geometricConcentrationClosed canonicalNSPressurePoissonBypassReceipt ≡ false
canonicalNSPressurePoissonBypassGeometricConcentrationClosedIsFalse = refl

canonicalNSPressurePoissonBypassPromotionGrantedIsFalse :
  promotionGranted canonicalNSPressurePoissonBypassReceipt ≡ false
canonicalNSPressurePoissonBypassPromotionGrantedIsFalse = refl

canonicalNSPressurePoissonBypassReceiptBoundaryIsCanonical :
  receiptBoundary canonicalNSPressurePoissonBypassReceipt ≡ receiptBoundaryText
canonicalNSPressurePoissonBypassReceiptBoundaryIsCanonical = refl

canonicalNSPressurePoissonBypassReceiptBoundaryParagraphIsCanonical :
  receiptBoundaryParagraph canonicalNSPressurePoissonBypassReceipt ≡ canonicalBoundaryText
canonicalNSPressurePoissonBypassReceiptBoundaryParagraphIsCanonical = refl
