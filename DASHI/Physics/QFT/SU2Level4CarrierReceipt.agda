module DASHI.Physics.QFT.SU2Level4CarrierReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- SU(2) level-4 carrier receipt.
--
-- This receipt records a narrow carrier-diagnostic surface:
--
-- * p2, conductor 4, is kept as a candidate lane for SU(2)_4
--   Chern-Simons data.
-- * p3, conductor 3, is kept as a level-rank candidate relating SU(2)_3
--   and SU(3)_1.
-- * p5, conductor 7, is recorded only as a diagnostic lane.
-- * the fermion-spin reading of SU(2)_4 is conditional on the separate
--   SU2kCSSpinStatisticsReceipt authority surface.
--
-- No exact Standard-Model promotion, exact G_DHR ~= G_SM promotion, or
-- unconditional fermion derivation is introduced here.

data PrimeLane : Set where
  p2Lane :
    PrimeLane

  p3Lane :
    PrimeLane

  p5Lane :
    PrimeLane

data CarrierReadingStatus : Set where
  chernSimonsCandidate :
    CarrierReadingStatus

  levelRankCandidate :
    CarrierReadingStatus

  diagnosticOnly :
    CarrierReadingStatus

data FermionSpinStatus : Set where
  conditionalOnSU2kCSSpinStatisticsReceipt :
    FermionSpinStatus

data SU2Level4Residual : Set where
  missingSU2kCSSpinStatisticsReceiptImport :
    SU2Level4Residual

  missingThreePlusOneDimensionalFermionDerivation :
    SU2Level4Residual

  missingExactStandardModelPromotion :
    SU2Level4Residual

  missingExactGDHREqualsGSMIdentification :
    SU2Level4Residual

canonicalSU2Level4Residuals :
  List SU2Level4Residual
canonicalSU2Level4Residuals =
  missingSU2kCSSpinStatisticsReceiptImport
  ∷ missingThreePlusOneDimensionalFermionDerivation
  ∷ missingExactStandardModelPromotion
  ∷ missingExactGDHREqualsGSMIdentification
  ∷ []

su2Level4ChernSimonsCandidateLabel : String
su2Level4ChernSimonsCandidateLabel =
  "p2 conductor-4 lane is recorded as an SU(2)_4 Chern-Simons candidate"

su2Level3SU3Level1LevelRankCandidateLabel : String
su2Level3SU3Level1LevelRankCandidateLabel =
  "p3 conductor-3 lane is recorded as an SU(2)_3 / SU(3)_1 level-rank candidate"

p5Conductor7DiagnosticLabel : String
p5Conductor7DiagnosticLabel =
  "p5 conductor-7 lane is retained only as a diagnostic carrier lane"

fermionSpinConditionalLabel : String
fermionSpinConditionalLabel =
  "SU(2)_4 gives a fermion-spin reading only conditional on SU2kCSSpinStatisticsReceipt"

noExactSMPromotionLabel : String
noExactSMPromotionLabel =
  "no exact Standard-Model promotion is claimed by this SU(2)_4 carrier receipt"

record PrimeLaneCarrierCandidate : Set where
  field
    lane :
      PrimeLane

    conductor :
      Nat

    targetTheory :
      String

    status :
      CarrierReadingStatus

    boundary :
      String

open PrimeLaneCarrierCandidate public

p2Conductor4SU2Level4Candidate :
  PrimeLaneCarrierCandidate
p2Conductor4SU2Level4Candidate =
  record
    { lane =
        p2Lane
    ; conductor =
        4
    ; targetTheory =
        "SU(2)_4 Chern-Simons"
    ; status =
        chernSimonsCandidate
    ; boundary =
        su2Level4ChernSimonsCandidateLabel
    }

p3Conductor3LevelRankCandidate :
  PrimeLaneCarrierCandidate
p3Conductor3LevelRankCandidate =
  record
    { lane =
        p3Lane
    ; conductor =
        3
    ; targetTheory =
        "SU(2)_3 / SU(3)_1 level-rank candidate"
    ; status =
        levelRankCandidate
    ; boundary =
        su2Level3SU3Level1LevelRankCandidateLabel
    }

p5Conductor7Diagnostic :
  PrimeLaneCarrierCandidate
p5Conductor7Diagnostic =
  record
    { lane =
        p5Lane
    ; conductor =
        7
    ; targetTheory =
        "conductor-7 diagnostic"
    ; status =
        diagnosticOnly
    ; boundary =
        p5Conductor7DiagnosticLabel
    }

record SU2Level4CarrierReceipt : Set where
  field
    p2Conductor4Lane :
      PrimeLaneCarrierCandidate

    p2Conductor4LaneIsCanonical :
      p2Conductor4Lane ≡ p2Conductor4SU2Level4Candidate

    p3Conductor3Lane :
      PrimeLaneCarrierCandidate

    p3Conductor3LaneIsCanonical :
      p3Conductor3Lane ≡ p3Conductor3LevelRankCandidate

    p5Conductor7Lane :
      PrimeLaneCarrierCandidate

    p5Conductor7LaneIsCanonical :
      p5Conductor7Lane ≡ p5Conductor7Diagnostic

    su2Level4ChernSimonsCandidate :
      Bool

    su2Level4ChernSimonsCandidateIsTrue :
      su2Level4ChernSimonsCandidate ≡ true

    p3LevelRankCandidate :
      Bool

    p3LevelRankCandidateIsTrue :
      p3LevelRankCandidate ≡ true

    p5Conductor7DiagnosticOnly :
      Bool

    p5Conductor7DiagnosticOnlyIsTrue :
      p5Conductor7DiagnosticOnly ≡ true

    fermionSpinStatus :
      FermionSpinStatus

    fermionSpinStatusIsConditional :
      fermionSpinStatus ≡ conditionalOnSU2kCSSpinStatisticsReceipt

    fermionSpinCondition :
      String

    fermionSpinConditionIsCanonical :
      fermionSpinCondition ≡ fermionSpinConditionalLabel

    su2Level4GivesFermionSpinUnconditionally :
      Bool

    su2Level4GivesFermionSpinUnconditionallyIsFalse :
      su2Level4GivesFermionSpinUnconditionally ≡ false

    exactStandardModelPromotion :
      Bool

    exactStandardModelPromotionIsFalse :
      exactStandardModelPromotion ≡ false

    exactGDHREqualsGSM :
      Bool

    exactGDHREqualsGSMIsFalse :
      exactGDHREqualsGSM ≡ false

    noExactSMPromotionBoundary :
      String

    noExactSMPromotionBoundaryIsCanonical :
      noExactSMPromotionBoundary ≡ noExactSMPromotionLabel

    residuals :
      List SU2Level4Residual

    residualsAreCanonical :
      residuals ≡ canonicalSU2Level4Residuals

    receiptBoundary :
      List String

open SU2Level4CarrierReceipt public

canonicalSU2Level4ReceiptBoundary :
  List String
canonicalSU2Level4ReceiptBoundary =
  su2Level4ChernSimonsCandidateLabel
  ∷ su2Level3SU3Level1LevelRankCandidateLabel
  ∷ p5Conductor7DiagnosticLabel
  ∷ fermionSpinConditionalLabel
  ∷ noExactSMPromotionLabel
  ∷ []

canonicalSU2Level4CarrierReceipt :
  SU2Level4CarrierReceipt
canonicalSU2Level4CarrierReceipt =
  record
    { p2Conductor4Lane =
        p2Conductor4SU2Level4Candidate
    ; p2Conductor4LaneIsCanonical =
        refl
    ; p3Conductor3Lane =
        p3Conductor3LevelRankCandidate
    ; p3Conductor3LaneIsCanonical =
        refl
    ; p5Conductor7Lane =
        p5Conductor7Diagnostic
    ; p5Conductor7LaneIsCanonical =
        refl
    ; su2Level4ChernSimonsCandidate =
        true
    ; su2Level4ChernSimonsCandidateIsTrue =
        refl
    ; p3LevelRankCandidate =
        true
    ; p3LevelRankCandidateIsTrue =
        refl
    ; p5Conductor7DiagnosticOnly =
        true
    ; p5Conductor7DiagnosticOnlyIsTrue =
        refl
    ; fermionSpinStatus =
        conditionalOnSU2kCSSpinStatisticsReceipt
    ; fermionSpinStatusIsConditional =
        refl
    ; fermionSpinCondition =
        fermionSpinConditionalLabel
    ; fermionSpinConditionIsCanonical =
        refl
    ; su2Level4GivesFermionSpinUnconditionally =
        false
    ; su2Level4GivesFermionSpinUnconditionallyIsFalse =
        refl
    ; exactStandardModelPromotion =
        false
    ; exactStandardModelPromotionIsFalse =
        refl
    ; exactGDHREqualsGSM =
        false
    ; exactGDHREqualsGSMIsFalse =
        refl
    ; noExactSMPromotionBoundary =
        noExactSMPromotionLabel
    ; noExactSMPromotionBoundaryIsCanonical =
        refl
    ; residuals =
        canonicalSU2Level4Residuals
    ; residualsAreCanonical =
        refl
    ; receiptBoundary =
        canonicalSU2Level4ReceiptBoundary
    }

p2LaneRecordedAsSU2Level4ChernSimonsCandidate :
  su2Level4ChernSimonsCandidate canonicalSU2Level4CarrierReceipt
  ≡
  true
p2LaneRecordedAsSU2Level4ChernSimonsCandidate =
  su2Level4ChernSimonsCandidateIsTrue canonicalSU2Level4CarrierReceipt

p3LaneRecordedAsLevelRankCandidate :
  p3LevelRankCandidate canonicalSU2Level4CarrierReceipt
  ≡
  true
p3LaneRecordedAsLevelRankCandidate =
  p3LevelRankCandidateIsTrue canonicalSU2Level4CarrierReceipt

p5LaneRecordedAsDiagnosticOnly :
  p5Conductor7DiagnosticOnly canonicalSU2Level4CarrierReceipt
  ≡
  true
p5LaneRecordedAsDiagnosticOnly =
  p5Conductor7DiagnosticOnlyIsTrue canonicalSU2Level4CarrierReceipt

su2Level4FermionSpinIsConditional :
  fermionSpinStatus canonicalSU2Level4CarrierReceipt
  ≡
  conditionalOnSU2kCSSpinStatisticsReceipt
su2Level4FermionSpinIsConditional =
  fermionSpinStatusIsConditional canonicalSU2Level4CarrierReceipt

su2Level4DoesNotPromoteExactSM :
  exactStandardModelPromotion canonicalSU2Level4CarrierReceipt
  ≡
  false
su2Level4DoesNotPromoteExactSM =
  exactStandardModelPromotionIsFalse canonicalSU2Level4CarrierReceipt
