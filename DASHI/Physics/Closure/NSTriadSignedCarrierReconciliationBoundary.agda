module DASHI.Physics.Closure.NSTriadSignedCarrierReconciliationBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Fail-closed Wall 1 signed-carrier reconciliation boundary.
--
-- This receipt records the reconciliation problem explicitly:
--   * the older optimistic signed chart is non-canonical until reconciled
--     with the newer fail-closed extraction;
--   * the active signed mod-2 carrier is gaugeable;
--   * the active signed spectral proxy is not I-K_N;
--   * theorem/full-NS/Clay promotion remains false;
--   * the missing theorem is corrected carrier identification before any
--     signed theorem promotion.
--
-- The file is candidate-only and records a boundary, not a proof.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

data NSTriadSignedCarrierReconciliationBoundaryStatus : Set where
  wall1SignedCarrierReconciliationBoundaryRecorded :
    NSTriadSignedCarrierReconciliationBoundaryStatus

data NSTriadSignedCarrierReconciliationBoundaryRow : Set where
  olderOptimisticSignedChartNonCanonicalRecorded :
    NSTriadSignedCarrierReconciliationBoundaryRow
  failClosedExtractionReconcilesCarrierRecorded :
    NSTriadSignedCarrierReconciliationBoundaryRow
  activeSignedMod2CarrierGaugeableRecorded :
    NSTriadSignedCarrierReconciliationBoundaryRow
  activeSignedSpectralProxyNotIKNRecorded :
    NSTriadSignedCarrierReconciliationBoundaryRow
  correctedCarrierIdentificationRequiredRecorded :
    NSTriadSignedCarrierReconciliationBoundaryRow
  failClosedPromotionWallRecorded :
    NSTriadSignedCarrierReconciliationBoundaryRow

canonicalNSTriadSignedCarrierReconciliationBoundaryRows :
  List NSTriadSignedCarrierReconciliationBoundaryRow
canonicalNSTriadSignedCarrierReconciliationBoundaryRows =
  olderOptimisticSignedChartNonCanonicalRecorded
  ∷ failClosedExtractionReconcilesCarrierRecorded
  ∷ activeSignedMod2CarrierGaugeableRecorded
  ∷ activeSignedSpectralProxyNotIKNRecorded
  ∷ correctedCarrierIdentificationRequiredRecorded
  ∷ failClosedPromotionWallRecorded
  ∷ []

nSTriadSignedCarrierReconciliationBoundaryRowCount : Nat
nSTriadSignedCarrierReconciliationBoundaryRowCount =
  listLength canonicalNSTriadSignedCarrierReconciliationBoundaryRows

nSTriadSignedCarrierReconciliationBoundaryRowCountIs6 :
  nSTriadSignedCarrierReconciliationBoundaryRowCount ≡ 6
nSTriadSignedCarrierReconciliationBoundaryRowCountIs6 = refl

data NSTriadSignedCarrierReconciliationBoundaryGap : Set where
  olderChartIsNotCanonicalYet :
    NSTriadSignedCarrierReconciliationBoundaryGap
  reconciliationWithFailClosedExtractionStillNeeded :
    NSTriadSignedCarrierReconciliationBoundaryGap
  activeSignedCarrierGaugeableButNotYetPromoted :
    NSTriadSignedCarrierReconciliationBoundaryGap
  activeSignedSpectralProxyIsNotIKN :
    NSTriadSignedCarrierReconciliationBoundaryGap
  theoremFullNSClayPromotionRemainFalse :
    NSTriadSignedCarrierReconciliationBoundaryGap

canonicalNSTriadSignedCarrierReconciliationBoundaryGaps :
  List NSTriadSignedCarrierReconciliationBoundaryGap
canonicalNSTriadSignedCarrierReconciliationBoundaryGaps =
  olderChartIsNotCanonicalYet
  ∷ reconciliationWithFailClosedExtractionStillNeeded
  ∷ activeSignedCarrierGaugeableButNotYetPromoted
  ∷ activeSignedSpectralProxyIsNotIKN
  ∷ theoremFullNSClayPromotionRemainFalse
  ∷ []

nSTriadSignedCarrierReconciliationBoundaryGapCount : Nat
nSTriadSignedCarrierReconciliationBoundaryGapCount =
  listLength canonicalNSTriadSignedCarrierReconciliationBoundaryGaps

nSTriadSignedCarrierReconciliationBoundaryGapCountIs5 :
  nSTriadSignedCarrierReconciliationBoundaryGapCount ≡ 5
nSTriadSignedCarrierReconciliationBoundaryGapCountIs5 = refl

canonicalTargetText : String
canonicalTargetText =
  "corrected carrier identification before signed theorem promotion"

canonicalOText : String
canonicalOText =
  "O: record the Wall 1 signed-carrier reconciliation boundary as a fail-closed receipt."

canonicalRText : String
canonicalRText =
  "R: mark the older optimistic signed chart non-canonical until reconciled with the newer fail-closed extraction, while keeping the active signed mod-2 carrier gaugeable and the active signed spectral proxy not I-K_N."

canonicalCText : String
canonicalCText =
  "C: export canonical rows, gaps, and false-promotion gates together with the corrected carrier-identification target."

canonicalSText : String
canonicalSText =
  "S: the active signed carrier is gaugeable, but the older optimistic chart is not canonical yet and the active signed spectral proxy is not I-K_N."

canonicalLText : String
canonicalLText =
  "L: older optimistic chart -> fail-closed extraction reconciliation -> active signed mod-2 gaugeability -> spectral proxy not I-K_N -> corrected carrier identification before signed theorem promotion."

canonicalPText : String
canonicalPText =
  "P: keep the signed-carrier route candidate-only until the carrier identification is corrected; do not promote theorem, full-NS, or Clay status."

canonicalGText : String
canonicalGText =
  "G: theorem, full-NS, and Clay promotion remain false."

canonicalFText : String
canonicalFText =
  "F: the missing theorem is corrected carrier identification before any signed theorem promotion."

record NSTriadSignedCarrierReconciliationBoundaryORCSLPGF : Set where
  constructor mkNSTriadSignedCarrierReconciliationBoundaryORCSLPGF
  field
    O : String
    OIsCanonical : O ≡ canonicalOText
    R : String
    RIsCanonical : R ≡ canonicalRText
    C : String
    CIsCanonical : C ≡ canonicalCText
    S : String
    SIsCanonical : S ≡ canonicalSText
    L : String
    LIsCanonical : L ≡ canonicalLText
    P : String
    PIsCanonical : P ≡ canonicalPText
    G : String
    GIsCanonical : G ≡ canonicalGText
    F : String
    FIsCanonical : F ≡ canonicalFText

open NSTriadSignedCarrierReconciliationBoundaryORCSLPGF public

canonicalNSTriadSignedCarrierReconciliationBoundaryORCSLPGF :
  NSTriadSignedCarrierReconciliationBoundaryORCSLPGF
canonicalNSTriadSignedCarrierReconciliationBoundaryORCSLPGF =
  mkNSTriadSignedCarrierReconciliationBoundaryORCSLPGF
    canonicalOText
    refl
    canonicalRText
    refl
    canonicalCText
    refl
    canonicalSText
    refl
    canonicalLText
    refl
    canonicalPText
    refl
    canonicalGText
    refl
    canonicalFText
    refl

data NSTriadSignedCarrierReconciliationBoundaryPromotion : Set where

promotionImpossibleHere :
  NSTriadSignedCarrierReconciliationBoundaryPromotion → ⊥
promotionImpossibleHere ()

record NSTriadSignedCarrierReconciliationBoundary : Setω where
  constructor mkNSTriadSignedCarrierReconciliationBoundary
  field
    status :
      NSTriadSignedCarrierReconciliationBoundaryStatus
    statusIsCanonical :
      status ≡ wall1SignedCarrierReconciliationBoundaryRecorded

    receiptName :
      String
    receiptNameIsCanonical :
      receiptName ≡ "NSTriadSignedCarrierReconciliationBoundary"

    targetIdentification :
      String
    targetIdentificationIsCanonical :
      targetIdentification ≡ canonicalTargetText

    candidateOnly :
      Bool
    candidateOnlyIsTrue :
      candidateOnly ≡ true

    failClosed :
      Bool
    failClosedIsTrue :
      failClosed ≡ true

    olderOptimisticSignedChartNonCanonical :
      Bool
    olderOptimisticSignedChartNonCanonicalIsTrue :
      olderOptimisticSignedChartNonCanonical ≡ true

    activeSignedMod2CarrierGaugeable :
      Bool
    activeSignedMod2CarrierGaugeableIsTrue :
      activeSignedMod2CarrierGaugeable ≡ true

    activeSignedSpectralProxyNotIKN :
      Bool
    activeSignedSpectralProxyNotIKNIsTrue :
      activeSignedSpectralProxyNotIKN ≡ true

    theoremPromoted :
      Bool
    theoremPromotedIsFalse :
      theoremPromoted ≡ false

    fullNSPromoted :
      Bool
    fullNSPromotedIsFalse :
      fullNSPromoted ≡ false

    clayPromoted :
      Bool
    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotionWitness :
      NSTriadSignedCarrierReconciliationBoundaryPromotion → ⊥

    orcslpgf :
      NSTriadSignedCarrierReconciliationBoundaryORCSLPGF
    orcslpgfIsCanonical :
      orcslpgf ≡ canonicalNSTriadSignedCarrierReconciliationBoundaryORCSLPGF

    rows :
      List NSTriadSignedCarrierReconciliationBoundaryRow
    rowsAreCanonical :
      rows ≡ canonicalNSTriadSignedCarrierReconciliationBoundaryRows
    rowCount :
      Nat
    rowCountIsCanonical :
      rowCount ≡ nSTriadSignedCarrierReconciliationBoundaryRowCount

    gaps :
      List NSTriadSignedCarrierReconciliationBoundaryGap
    gapsAreCanonical :
      gaps ≡ canonicalNSTriadSignedCarrierReconciliationBoundaryGaps
    gapCount :
      Nat
    gapCountIsCanonical :
      gapCount ≡ nSTriadSignedCarrierReconciliationBoundaryGapCount

    statement :
      String
    statementIsCanonical :
      statement ≡
      "Candidate-only Wall 1 signed-carrier reconciliation boundary: the older optimistic signed chart is non-canonical until reconciled with the newer fail-closed extraction, the active signed mod-2 carrier is gaugeable, the active signed spectral proxy is not I-K_N, and corrected carrier identification is the missing theorem before any signed theorem promotion."

canonicalNSTriadSignedCarrierReconciliationBoundary :
  NSTriadSignedCarrierReconciliationBoundary
canonicalNSTriadSignedCarrierReconciliationBoundary =
  mkNSTriadSignedCarrierReconciliationBoundary
    wall1SignedCarrierReconciliationBoundaryRecorded
    refl
    "NSTriadSignedCarrierReconciliationBoundary"
    refl
    canonicalTargetText
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
    promotionImpossibleHere
    canonicalNSTriadSignedCarrierReconciliationBoundaryORCSLPGF
    refl
    canonicalNSTriadSignedCarrierReconciliationBoundaryRows
    refl
    nSTriadSignedCarrierReconciliationBoundaryRowCount
    refl
    canonicalNSTriadSignedCarrierReconciliationBoundaryGaps
    refl
    nSTriadSignedCarrierReconciliationBoundaryGapCount
    refl
    "Candidate-only Wall 1 signed-carrier reconciliation boundary: the older optimistic signed chart is non-canonical until reconciled with the newer fail-closed extraction, the active signed mod-2 carrier is gaugeable, the active signed spectral proxy is not I-K_N, and corrected carrier identification is the missing theorem before any signed theorem promotion."
    refl
