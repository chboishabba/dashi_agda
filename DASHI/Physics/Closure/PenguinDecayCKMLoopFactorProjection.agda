module DASHI.Physics.Closure.PenguinDecayCKMLoopFactorProjection where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CKMCarrierDerived as CKM
import DASHI.Physics.Closure.CKMUnitarityFromCarrier as CKMU
import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.Closure.PenguinDecayProjectionDefectReceipt as Penguin
import DASHI.Physics.Closure.PenguinDecaySMBaselineAuthority as SMBaseline

------------------------------------------------------------------------
-- b -> s mu+ mu- CKM loop-factor projection.
--
-- This receipt is deliberately narrow.  It wires the existing penguin
-- b -> s mu+ mu- loop-only surface to the carrier-derived CKM witness for
-- the Vtb Vts* bookkeeping factor.  Wilson coefficients, numerical loop
-- functions, form factors, and SM baseline authority remain external and
-- fail-closed through PenguinDecaySMBaselineAuthority.

data CKMLoopFactorProjectionStatus : Set where
  bToSMuMuCarrierCKMLoopFactorWiredExternalWilsonAuthority :
    CKMLoopFactorProjectionStatus

data CKMLoopFactorRole : Set where
  vtbVtsStarCarrierFactor :
    CKMLoopFactorRole

data CKMLoopAmplitudeUse : Set where
  loopAmplitudeUsesCarrierDerivedCKMFactor :
    CKMLoopAmplitudeUse

data WilsonCoefficientAuthorityBoundary : Set where
  wilsonCoefficientAuthorityExternal :
    WilsonCoefficientAuthorityBoundary
  wilsonCoefficientValuesNotConstructedHere :
    WilsonCoefficientAuthorityBoundary
  effectiveHamiltonianConventionNotConstructedHere :
    WilsonCoefficientAuthorityBoundary
  smBaselineComparisonStillBlocked :
    WilsonCoefficientAuthorityBoundary
  ckmSourceCommitAuthorityRequired :
    WilsonCoefficientAuthorityBoundary

canonicalWilsonCoefficientAuthorityBoundaries :
  List WilsonCoefficientAuthorityBoundary
canonicalWilsonCoefficientAuthorityBoundaries =
  wilsonCoefficientAuthorityExternal
  ∷ wilsonCoefficientValuesNotConstructedHere
  ∷ effectiveHamiltonianConventionNotConstructedHere
  ∷ smBaselineComparisonStillBlocked
  ∷ ckmSourceCommitAuthorityRequired
  ∷ []

data WilsonCoefficientAuthorityToken : Set where

wilsonCoefficientAuthorityTokenImpossibleHere :
  WilsonCoefficientAuthorityToken →
  ⊥
wilsonCoefficientAuthorityTokenImpossibleHere ()

record BToSMuMuCKMLoopFactorProjectionReceipt : Setω where
  field
    status :
      CKMLoopFactorProjectionStatus

    penguinReceipt :
      Penguin.PenguinDecayProjectionDefectReceipt

    penguinReceiptIsCanonical :
      penguinReceipt
      ≡
      Penguin.canonicalPenguinDecayProjectionDefectReceipt

    smBaselineAuthorityDiagnostic :
      SMBaseline.SMBaselineAuthorityRequestDiagnostic

    smBaselineAuthorityDiagnosticIsCanonical :
      smBaselineAuthorityDiagnostic
      ≡
      SMBaseline.canonicalSMBaselineAuthorityRequestDiagnostic

    selectedDecay :
      Penguin.RarePenguinDecay

    selectedDecayIsBToSLeptonPair :
      selectedDecay
      ≡
      Penguin.bToSLeptonPair

    selectedLeptonPair :
      SMBaseline.TargetLeptonPair

    selectedLeptonPairIsMuPlusMuMinus :
      selectedLeptonPair
      ≡
      SMBaseline.muPlusMuMinus

    smTransport :
      List Penguin.TransportRoute

    smTransportIsLoopOnly :
      smTransport
      ≡
      (Penguin.penguinLoopRoute ∷ Penguin.boxLoopRoute ∷ [])

    smAmplitudeCell :
      Penguin.AmplitudeCell

    smAmplitudeCellIsCanonical :
      smAmplitudeCell
      ≡
      Penguin.smCell Penguin.bToSLeptonPair

    smAmplitudeProjectsToSM :
      Penguin.projectToSM smAmplitudeCell
      ≡
      Penguin.standardModelSurface

    loopFactorRole :
      CKMLoopFactorRole

    loopFactorRoleIsVtbVtsStar :
      loopFactorRole
      ≡
      vtbVtsStarCarrierFactor

    loopAmplitudeUse :
      CKMLoopAmplitudeUse

    loopAmplitudeUseIsCarrierDerived :
      loopAmplitudeUse
      ≡
      loopAmplitudeUsesCarrierDerivedCKMFactor

    vtbVtsStarCarrierFactorMatrix :
      Matter.MixingMatrix

    vtbVtsStarCarrierFactorMatrixIsCarrierDerived :
      vtbVtsStarCarrierFactorMatrix
      ≡
      CKM.ckmCarrierMatrix CKM.canonicalCKMCarrierDerived

    vtbVtsStarCarrierFactorMatrixIsUnitaryCarrier :
      vtbVtsStarCarrierFactorMatrix
      ≡
      CKMU.carrierCKMMatrix CKMU.canonicalCKMUnitary

    carrierDerivedCKMBoundary :
      List String

    carrierDerivedCKMBoundaryIsCanonical :
      carrierDerivedCKMBoundary
      ≡
      CKM.carrierDerivedBoundary CKM.canonicalCKMCarrierDerived

    carrierUnitaryBoundary :
      List String

    carrierUnitaryBoundaryIsCanonical :
      carrierUnitaryBoundary
      ≡
      CKMU.unitaryBoundary CKMU.canonicalCKMUnitary

    ckmSourceCommitSlot :
      String

    ckmSourceCommitSlotIsRequired :
      ckmSourceCommitSlot
      ≡
      "required: CKM carrier source commit or immutable external source revision"

    ckmSourceAuthoritySlot :
      String

    ckmSourceAuthoritySlotIsRequired :
      ckmSourceAuthoritySlot
      ≡
      "required: authority binding for Vtb Vts* loop-factor inputs"

    ckmSourceCommitAcceptedHere :
      Bool

    ckmSourceCommitAcceptedHereIsFalse :
      ckmSourceCommitAcceptedHere
      ≡
      false

    requiredSMBaselineAuthorityFields :
      List SMBaseline.SMBaselineAuthorityField

    requiredSMBaselineAuthorityFieldsAreCanonical :
      requiredSMBaselineAuthorityFields
      ≡
      SMBaseline.canonicalSMBaselineAuthorityFields

    wilsonCoefficientAuthorityBoundary :
      List WilsonCoefficientAuthorityBoundary

    wilsonCoefficientAuthorityBoundaryIsCanonical :
      wilsonCoefficientAuthorityBoundary
      ≡
      canonicalWilsonCoefficientAuthorityBoundaries

    wilsonCoefficientAuthorityConstructible :
      Bool

    wilsonCoefficientAuthorityConstructibleIsFalse :
      wilsonCoefficientAuthorityConstructible
      ≡
      false

    wilsonCoefficientAuthorityRequired :
      Bool

    wilsonCoefficientAuthorityRequiredIsTrue :
      wilsonCoefficientAuthorityRequired
      ≡
      true

    empiricalComparisonConstructible :
      Bool

    empiricalComparisonConstructibleIsFalse :
      empiricalComparisonConstructible
      ≡
      false

    promotionConstructed :
      Bool

    promotionConstructedIsFalse :
      promotionConstructed
      ≡
      false

    noWilsonCoefficientAuthorityTokenHere :
      WilsonCoefficientAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open BToSMuMuCKMLoopFactorProjectionReceipt public

canonicalBToSMuMuCKMLoopFactorProjectionReceipt :
  BToSMuMuCKMLoopFactorProjectionReceipt
canonicalBToSMuMuCKMLoopFactorProjectionReceipt =
  record
    { status =
        bToSMuMuCarrierCKMLoopFactorWiredExternalWilsonAuthority
    ; penguinReceipt =
        Penguin.canonicalPenguinDecayProjectionDefectReceipt
    ; penguinReceiptIsCanonical =
        refl
    ; smBaselineAuthorityDiagnostic =
        SMBaseline.canonicalSMBaselineAuthorityRequestDiagnostic
    ; smBaselineAuthorityDiagnosticIsCanonical =
        refl
    ; selectedDecay =
        Penguin.bToSLeptonPair
    ; selectedDecayIsBToSLeptonPair =
        refl
    ; selectedLeptonPair =
        SMBaseline.muPlusMuMinus
    ; selectedLeptonPairIsMuPlusMuMinus =
        refl
    ; smTransport =
        Penguin.acceptedSMTransport Penguin.bToSLeptonPair
    ; smTransportIsLoopOnly =
        refl
    ; smAmplitudeCell =
        Penguin.smCell Penguin.bToSLeptonPair
    ; smAmplitudeCellIsCanonical =
        refl
    ; smAmplitudeProjectsToSM =
        refl
    ; loopFactorRole =
        vtbVtsStarCarrierFactor
    ; loopFactorRoleIsVtbVtsStar =
        refl
    ; loopAmplitudeUse =
        loopAmplitudeUsesCarrierDerivedCKMFactor
    ; loopAmplitudeUseIsCarrierDerived =
        refl
    ; vtbVtsStarCarrierFactorMatrix =
        CKM.ckmCarrierMatrix CKM.canonicalCKMCarrierDerived
    ; vtbVtsStarCarrierFactorMatrixIsCarrierDerived =
        refl
    ; vtbVtsStarCarrierFactorMatrixIsUnitaryCarrier =
        refl
    ; carrierDerivedCKMBoundary =
        CKM.carrierDerivedBoundary CKM.canonicalCKMCarrierDerived
    ; carrierDerivedCKMBoundaryIsCanonical =
        refl
    ; carrierUnitaryBoundary =
        CKMU.unitaryBoundary CKMU.canonicalCKMUnitary
    ; carrierUnitaryBoundaryIsCanonical =
        refl
    ; ckmSourceCommitSlot =
        "required: CKM carrier source commit or immutable external source revision"
    ; ckmSourceCommitSlotIsRequired =
        refl
    ; ckmSourceAuthoritySlot =
        "required: authority binding for Vtb Vts* loop-factor inputs"
    ; ckmSourceAuthoritySlotIsRequired =
        refl
    ; ckmSourceCommitAcceptedHere =
        false
    ; ckmSourceCommitAcceptedHereIsFalse =
        refl
    ; requiredSMBaselineAuthorityFields =
        SMBaseline.canonicalSMBaselineAuthorityFields
    ; requiredSMBaselineAuthorityFieldsAreCanonical =
        refl
    ; wilsonCoefficientAuthorityBoundary =
        canonicalWilsonCoefficientAuthorityBoundaries
    ; wilsonCoefficientAuthorityBoundaryIsCanonical =
        refl
    ; wilsonCoefficientAuthorityConstructible =
        false
    ; wilsonCoefficientAuthorityConstructibleIsFalse =
        refl
    ; wilsonCoefficientAuthorityRequired =
        true
    ; wilsonCoefficientAuthorityRequiredIsTrue =
        refl
    ; empiricalComparisonConstructible =
        false
    ; empiricalComparisonConstructibleIsFalse =
        refl
    ; promotionConstructed =
        false
    ; promotionConstructedIsFalse =
        refl
    ; noWilsonCoefficientAuthorityTokenHere =
        wilsonCoefficientAuthorityTokenImpossibleHere
    ; receiptBoundary =
        "b -> s mu+ mu- is selected from the existing penguin projection-defect receipt"
        ∷ "The selected Standard-Model transport is penguin-loop and box-loop only"
        ∷ "The Vtb Vts* loop-factor role is wired to the carrier-derived CKM matrix receipt"
        ∷ "The same CKM carrier is cross-checked against the carrier unitarity receipt"
        ∷ "The CKM source commit slot remains an external immutable revision requirement"
        ∷ "Wilson coefficients, effective-Hamiltonian convention, numerical loop functions, and SM baseline authority are external"
        ∷ "No accepted Wilson authority token, empirical comparison, anomaly claim, or promotion is constructed here"
        ∷ []
    }

canonicalProjectionUsesCarrierDerivedCKM :
  vtbVtsStarCarrierFactorMatrix
    canonicalBToSMuMuCKMLoopFactorProjectionReceipt
  ≡
  CKM.ckmCarrierMatrix CKM.canonicalCKMCarrierDerived
canonicalProjectionUsesCarrierDerivedCKM =
  refl

canonicalProjectionWilsonAuthorityFailClosed :
  wilsonCoefficientAuthorityConstructible
    canonicalBToSMuMuCKMLoopFactorProjectionReceipt
  ≡
  false
canonicalProjectionWilsonAuthorityFailClosed =
  refl

canonicalProjectionNoEmpiricalComparison :
  empiricalComparisonConstructible
    canonicalBToSMuMuCKMLoopFactorProjectionReceipt
  ≡
  false
canonicalProjectionNoEmpiricalComparison =
  refl
