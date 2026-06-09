module DASHI.Physics.Closure.CKMVusCarrierPredictionTargetReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CKMCarrierDerived as CKMD
import DASHI.Physics.Closure.MatterRepresentationReceiptSurface as Matter
import DASHI.Physics.Closure.YukawaDHRIntertwinerCompatibility as YDHR

------------------------------------------------------------------------
-- First non-identity CKM prediction target: |V_us|.
--
-- The current carrier-derived CKM matrix is the identity matrix, so its
-- carrier v12 entry is zero.  This receipt records |V_us| as the first
-- non-identity physical CKM target and compares it with the PDG-sized
-- reference value 0.225 without asserting that the current carrier identity
-- matrix physically matches that value.

data CKMVusCarrierPredictionTargetStatus : Set where
  vusCarrierTargetRecordedComparisonOnly :
    CKMVusCarrierPredictionTargetStatus

data CKMVusCarrierTargetBlocker : Set where
  missingAcceptedAlphaCouplingForSymbolicVus :
    CKMVusCarrierTargetBlocker

  missingOffDiagonalYukawaCouplingEvaluation :
    CKMVusCarrierTargetBlocker

  missingNonIdentityPhysicalYukawaEigenbasis :
    CKMVusCarrierTargetBlocker
  missingExactPhysicalCKMProductBeyondIdentityCarrier :
    CKMVusCarrierTargetBlocker
  missingPDGAuthorityBindingForExactVus :
    CKMVusCarrierTargetBlocker
  missingApproximationErrorBoundToPDGValue :
    CKMVusCarrierTargetBlocker

canonicalCKMVusCarrierTargetBlockers :
  List CKMVusCarrierTargetBlocker
canonicalCKMVusCarrierTargetBlockers =
  missingAcceptedAlphaCouplingForSymbolicVus
  ∷ missingOffDiagonalYukawaCouplingEvaluation
  ∷ missingNonIdentityPhysicalYukawaEigenbasis
  ∷ missingExactPhysicalCKMProductBeyondIdentityCarrier
  ∷ missingPDGAuthorityBindingForExactVus
  ∷ missingApproximationErrorBoundToPDGValue
  ∷ []

data CKMVusPredictionObservable : Set where
  predictVus :
    CKMVusPredictionObservable

record CKMVusComparisonTarget : Set where
  constructor ckmVusComparisonTarget
  field
    observable :
      CKMVusPredictionObservable

    authorityLabel :
      String

    recordedAsComparisonOnly :
      Bool

    recordedAsComparisonOnlyIsTrue :
      recordedAsComparisonOnly ≡ true

    derivedByCarrier :
      Bool

    derivedByCarrierIsFalse :
      derivedByCarrier ≡ false

open CKMVusComparisonTarget public

pdg2025VusComparisonTarget :
  CKMVusComparisonTarget
pdg2025VusComparisonTarget =
  ckmVusComparisonTarget
    predictVus
    "PDG-2025 CKM |Vus| comparison target"
    true
    refl
    false
    refl

data CKMVusSymbolicParameter : Set where
  vusAlphaParameter :
    CKMVusSymbolicParameter

  vusOffDiagonalCouplingParameter :
    CKMVusSymbolicParameter

canonicalCKMVusSymbolicParameters :
  List CKMVusSymbolicParameter
canonicalCKMVusSymbolicParameters =
  vusAlphaParameter
  ∷ vusOffDiagonalCouplingParameter
  ∷ []

symbolicVusAlphaCouplingFormula :
  String
symbolicVusAlphaCouplingFormula =
  "|V_us|_target(alpha,g_12)=alpha*g_12"

record CKMVusOffDiagonalYukawaTargetData : Setω where
  field
    carrierDHRYukawaFormulaSurface :
      YDHR.CarrierDHRYukawaFormulaSurface

    carrierDHRYukawaFormulaSurfaceIsCanonical :
      Bool

    carrierDHRYukawaFormulaSurfaceIsCanonicalIsTrue :
      carrierDHRYukawaFormulaSurfaceIsCanonical ≡ true

    sourceGeneration :
      YDHR.YukawaGenerationIndex

    sourceGenerationIsFirst :
      sourceGeneration ≡ YDHR.firstGeneration

    targetGeneration :
      YDHR.YukawaGenerationIndex

    targetGenerationIsSecond :
      targetGeneration ≡ YDHR.secondGeneration

    upOffDiagonalYukawaEntry :
      Matter.MixingGaussianRationalDatum

    upOffDiagonalYukawaEntryIsFormulaEntry :
      upOffDiagonalYukawaEntry
      ≡
      YDHR.upFormulaEntry
        carrierDHRYukawaFormulaSurface
        sourceGeneration
        targetGeneration

    downOffDiagonalYukawaEntry :
      Matter.MixingGaussianRationalDatum

    downOffDiagonalYukawaEntryIsFormulaEntry :
      downOffDiagonalYukawaEntry
      ≡
      YDHR.downFormulaEntry
        carrierDHRYukawaFormulaSurface
        sourceGeneration
        targetGeneration

    currentCarrierOffDiagonalEntriesAreZero :
      Bool

    currentCarrierOffDiagonalEntriesAreZeroIsTrue :
      currentCarrierOffDiagonalEntriesAreZero ≡ true

    symbolicParameters :
      List CKMVusSymbolicParameter

    symbolicParametersAreCanonical :
      symbolicParameters ≡ canonicalCKMVusSymbolicParameters

    symbolicAlphaCouplingFormula :
      String

    symbolicAlphaCouplingFormulaIsCanonical :
      symbolicAlphaCouplingFormula
      ≡
      symbolicVusAlphaCouplingFormula

    symbolicTargetIsNonIdentity :
      Bool

    symbolicTargetIsNonIdentityIsTrue :
      symbolicTargetIsNonIdentity ≡ true

    alphaCouplingValueAccepted :
      Bool

    alphaCouplingValueAcceptedIsFalse :
      alphaCouplingValueAccepted ≡ false

    offDiagonalTargetBoundary :
      List String

open CKMVusOffDiagonalYukawaTargetData public

canonicalCKMVusOffDiagonalYukawaTargetData :
  CKMVusOffDiagonalYukawaTargetData
canonicalCKMVusOffDiagonalYukawaTargetData =
  record
    { carrierDHRYukawaFormulaSurface =
        YDHR.canonicalCarrierDHRYukawaFormulaSurface
    ; carrierDHRYukawaFormulaSurfaceIsCanonical =
        true
    ; carrierDHRYukawaFormulaSurfaceIsCanonicalIsTrue =
        refl
    ; sourceGeneration =
        YDHR.firstGeneration
    ; sourceGenerationIsFirst =
        refl
    ; targetGeneration =
        YDHR.secondGeneration
    ; targetGenerationIsSecond =
        refl
    ; upOffDiagonalYukawaEntry =
        YDHR.upFormulaEntry
          YDHR.canonicalCarrierDHRYukawaFormulaSurface
          YDHR.firstGeneration
          YDHR.secondGeneration
    ; upOffDiagonalYukawaEntryIsFormulaEntry =
        refl
    ; downOffDiagonalYukawaEntry =
        YDHR.downFormulaEntry
          YDHR.canonicalCarrierDHRYukawaFormulaSurface
          YDHR.firstGeneration
          YDHR.secondGeneration
    ; downOffDiagonalYukawaEntryIsFormulaEntry =
        refl
    ; currentCarrierOffDiagonalEntriesAreZero =
        true
    ; currentCarrierOffDiagonalEntriesAreZeroIsTrue =
        refl
    ; symbolicParameters =
        canonicalCKMVusSymbolicParameters
    ; symbolicParametersAreCanonical =
        refl
    ; symbolicAlphaCouplingFormula =
        symbolicVusAlphaCouplingFormula
    ; symbolicAlphaCouplingFormulaIsCanonical =
        refl
    ; symbolicTargetIsNonIdentity =
        true
    ; symbolicTargetIsNonIdentityIsTrue =
        refl
    ; alphaCouplingValueAccepted =
        false
    ; alphaCouplingValueAcceptedIsFalse =
        refl
    ; offDiagonalTargetBoundary =
        "The current carrier formula surface exposes first-second up/down Yukawa entries as off-diagonal target data"
        ∷ "Those entries are zero on the present diagonal carrier, so they do not yet produce a physical V_us value"
        ∷ "The first symbolic non-identity V_us target is recorded as |V_us|_target(alpha,g_12)=alpha*g_12"
        ∷ "No accepted alpha value, off-diagonal coupling value, or physical CKM match is supplied here"
        ∷ []
    }

pdgApproxVusSignedDatum :
  Matter.MixingSignedRationalDatum
pdgApproxVusSignedDatum =
  Matter.mixingSignedRationalDatum 225 1000 true

pdgApproxVusGaussianDatum :
  Matter.MixingGaussianRationalDatum
pdgApproxVusGaussianDatum =
  Matter.mixingGaussianRationalDatum
    pdgApproxVusSignedDatum
    Matter.zeroMixingSignedRationalDatum

data AcceptedExactPhysicalVusMatch : Set where

acceptedExactPhysicalVusMatchImpossibleHere :
  AcceptedExactPhysicalVusMatch →
  ⊥
acceptedExactPhysicalVusMatchImpossibleHere ()

record CKMVusCarrierPredictionTargetReceipt : Setω where
  field
    status :
      CKMVusCarrierPredictionTargetStatus

    frontierReceipt :
      String

    frontierReceiptIsLocalVusTarget :
      frontierReceipt
      ≡
      "local CKM Vus carrier prediction target receipt"

    carrierDerivedReceipt :
      CKMD.CKMCarrierDerivedReceipt

    carrierMatrix :
      Matter.MixingMatrix

    carrierMatrixIsCurrentCarrierDerived :
      carrierMatrix
      ≡
      CKMD.ckmCarrierMatrix carrierDerivedReceipt

    carrierMatrixIsIdentity :
      carrierMatrix ≡ Matter.identityMixingMatrix

    observable :
      CKMVusPredictionObservable

    observableIsVus :
      observable ≡ predictVus

    comparisonTarget :
      CKMVusComparisonTarget

    comparisonTargetIsPDGVus :
      comparisonTarget ≡ pdg2025VusComparisonTarget

    comparisonTargetRemainsComparisonOnly :
      recordedAsComparisonOnly comparisonTarget
      ≡
      true

    comparisonTargetDerivedByCarrierIsFalse :
      derivedByCarrier comparisonTarget
      ≡
      false

    carrierVusEntry :
      Matter.MixingGaussianRationalDatum

    carrierVusEntryIsMatrixV12 :
      carrierVusEntry ≡ Matter.v12 carrierMatrix

    carrierVusEntryIsZero :
      carrierVusEntry ≡ Matter.zeroMixingGaussianRationalDatum

    offDiagonalYukawaTargetData :
      CKMVusOffDiagonalYukawaTargetData

    offDiagonalYukawaTargetDataIsCanonical :
      Bool

    offDiagonalYukawaTargetDataIsCanonicalIsTrue :
      offDiagonalYukawaTargetDataIsCanonical ≡ true

    offDiagonalYukawaEntriesCurrentlyZero :
      currentCarrierOffDiagonalEntriesAreZero
        offDiagonalYukawaTargetData
      ≡
      true

    symbolicVusTargetFormula :
      String

    symbolicVusTargetFormulaIsAlphaCoupling :
      symbolicVusTargetFormula
      ≡
      symbolicAlphaCouplingFormula offDiagonalYukawaTargetData

    symbolicVusTargetFormulaIsCanonical :
      symbolicVusTargetFormula
      ≡
      symbolicVusAlphaCouplingFormula

    symbolicVusTargetIsNonIdentity :
      symbolicTargetIsNonIdentity offDiagonalYukawaTargetData
      ≡
      true

    alphaCouplingAcceptedForVus :
      Bool

    alphaCouplingAcceptedForVusIsFalse :
      alphaCouplingAcceptedForVus ≡ false

    pdgApproxVus :
      Matter.MixingGaussianRationalDatum

    pdgApproxVusIsZeroPointTwoTwoFive :
      pdgApproxVus ≡ pdgApproxVusGaussianDatum

    pdgApproxVusLabel :
      String

    pdgApproxVusLabelIsCanonical :
      pdgApproxVusLabel ≡ "PDG approximate |V_us| comparison value 0.225"

    nonIdentityTargetRecorded :
      Bool

    nonIdentityTargetRecordedIsTrue :
      nonIdentityTargetRecorded ≡ true

    currentCarrierValueIsIdentityZero :
      Bool

    currentCarrierValueIsIdentityZeroIsTrue :
      currentCarrierValueIsIdentityZero ≡ true

    exactPhysicalMatchClaimed :
      Bool

    exactPhysicalMatchClaimedIsFalse :
      exactPhysicalMatchClaimed ≡ false

    physicalCKMPromotionConstructed :
      Bool

    physicalCKMPromotionConstructedIsFalse :
      physicalCKMPromotionConstructed ≡ false

    blockers :
      List CKMVusCarrierTargetBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCKMVusCarrierTargetBlockers

    acceptedExactPhysicalVusMatchBlocked :
      AcceptedExactPhysicalVusMatch →
      ⊥

    receiptBoundary :
      List String

open CKMVusCarrierPredictionTargetReceipt public

canonicalCKMVusCarrierPredictionTargetReceipt :
  CKMVusCarrierPredictionTargetReceipt
canonicalCKMVusCarrierPredictionTargetReceipt =
  record
    { status =
        vusCarrierTargetRecordedComparisonOnly
    ; frontierReceipt =
        "local CKM Vus carrier prediction target receipt"
    ; frontierReceiptIsLocalVusTarget =
        refl
    ; carrierDerivedReceipt =
        CKMD.canonicalCKMCarrierDerived
    ; carrierMatrix =
        CKMD.ckmCarrierMatrix CKMD.canonicalCKMCarrierDerived
    ; carrierMatrixIsCurrentCarrierDerived =
        refl
    ; carrierMatrixIsIdentity =
        refl
    ; observable =
        predictVus
    ; observableIsVus =
        refl
    ; comparisonTarget =
        pdg2025VusComparisonTarget
    ; comparisonTargetIsPDGVus =
        refl
    ; comparisonTargetRemainsComparisonOnly =
        refl
    ; comparisonTargetDerivedByCarrierIsFalse =
        refl
    ; carrierVusEntry =
        Matter.v12 (CKMD.ckmCarrierMatrix CKMD.canonicalCKMCarrierDerived)
    ; carrierVusEntryIsMatrixV12 =
        refl
    ; carrierVusEntryIsZero =
        refl
    ; offDiagonalYukawaTargetData =
        canonicalCKMVusOffDiagonalYukawaTargetData
    ; offDiagonalYukawaTargetDataIsCanonical =
        true
    ; offDiagonalYukawaTargetDataIsCanonicalIsTrue =
        refl
    ; offDiagonalYukawaEntriesCurrentlyZero =
        refl
    ; symbolicVusTargetFormula =
        symbolicVusAlphaCouplingFormula
    ; symbolicVusTargetFormulaIsAlphaCoupling =
        refl
    ; symbolicVusTargetFormulaIsCanonical =
        refl
    ; symbolicVusTargetIsNonIdentity =
        refl
    ; alphaCouplingAcceptedForVus =
        false
    ; alphaCouplingAcceptedForVusIsFalse =
        refl
    ; pdgApproxVus =
        pdgApproxVusGaussianDatum
    ; pdgApproxVusIsZeroPointTwoTwoFive =
        refl
    ; pdgApproxVusLabel =
        "PDG approximate |V_us| comparison value 0.225"
    ; pdgApproxVusLabelIsCanonical =
        refl
    ; nonIdentityTargetRecorded =
        true
    ; nonIdentityTargetRecordedIsTrue =
        refl
    ; currentCarrierValueIsIdentityZero =
        true
    ; currentCarrierValueIsIdentityZeroIsTrue =
        refl
    ; exactPhysicalMatchClaimed =
        false
    ; exactPhysicalMatchClaimedIsFalse =
        refl
    ; physicalCKMPromotionConstructed =
        false
    ; physicalCKMPromotionConstructedIsFalse =
        refl
    ; blockers =
        canonicalCKMVusCarrierTargetBlockers
    ; blockersAreCanonical =
        refl
    ; acceptedExactPhysicalVusMatchBlocked =
        acceptedExactPhysicalVusMatchImpossibleHere
    ; receiptBoundary =
        "|V_us| is recorded as the first non-identity CKM prediction target"
        ∷ "The current carrier-derived CKM matrix is still the identity matrix, so its v12 entry is zero"
        ∷ "The receipt consumes first-second off-diagonal up/down Yukawa target data from the carrier DHR Yukawa formula surface"
        ∷ "The first symbolic non-identity target is |V_us|_target(alpha,g_12)=alpha*g_12"
        ∷ "The alpha/coupling target is symbolic only; no accepted alpha value or off-diagonal coupling evaluation is supplied"
        ∷ "The PDG-sized value 0.225 is recorded as an approximate comparison target only"
        ∷ "No exact physical CKM match, non-identity physical diagonalizer, approximation-error bound, or promotion is constructed here"
        ∷ []
    }

ckmVusCarrierTargetRecordsNonIdentityTarget :
  nonIdentityTargetRecorded canonicalCKMVusCarrierPredictionTargetReceipt
  ≡
  true
ckmVusCarrierTargetRecordsNonIdentityTarget =
  refl

ckmVusCarrierTargetCurrentCarrierVusIsZero :
  carrierVusEntry canonicalCKMVusCarrierPredictionTargetReceipt
  ≡
  Matter.zeroMixingGaussianRationalDatum
ckmVusCarrierTargetCurrentCarrierVusIsZero =
  refl

ckmVusCarrierTargetDoesNotClaimExactPhysicalMatch :
  exactPhysicalMatchClaimed canonicalCKMVusCarrierPredictionTargetReceipt
  ≡
  false
ckmVusCarrierTargetDoesNotClaimExactPhysicalMatch =
  refl

ckmVusSymbolicTargetIsNonIdentity :
  symbolicTargetIsNonIdentity
    (offDiagonalYukawaTargetData
      canonicalCKMVusCarrierPredictionTargetReceipt)
  ≡
  true
ckmVusSymbolicTargetIsNonIdentity =
  symbolicVusTargetIsNonIdentity
    canonicalCKMVusCarrierPredictionTargetReceipt

ckmVusAlphaCouplingAcceptedStillFalse :
  alphaCouplingAcceptedForVus
    canonicalCKMVusCarrierPredictionTargetReceipt
  ≡
  false
ckmVusAlphaCouplingAcceptedStillFalse =
  refl
