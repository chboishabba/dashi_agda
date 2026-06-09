module DASHI.Physics.Closure.CKMVcbDemotionReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- CKM |Vcb| demotion receipt.
--
-- This receipt records that a |Vcb| value obtained from
-- |Vcb| = A * lambda^2 with A = 0.8086 is a Wolfenstein-parametrisation
-- tautology using PDG input, not an independent carrier prediction.

data CKMVcbStatus : Set where
  pdgTautology :
    CKMVcbStatus

data CKMVcbDemotionBlocker : Set where
  pdgAInputNotDerivedFromCarrier :
    CKMVcbDemotionBlocker

  wolfensteinIdentityNotIndependentPrediction :
    CKMVcbDemotionBlocker

  noCarrierArithmeticReceiptForA :
    CKMVcbDemotionBlocker

canonicalCKMVcbDemotionBlockers :
  List CKMVcbDemotionBlocker
canonicalCKMVcbDemotionBlockers =
  pdgAInputNotDerivedFromCarrier
  ∷ wolfensteinIdentityNotIndependentPrediction
  ∷ noCarrierArithmeticReceiptForA
  ∷ []

data CKMVcbCarrierPrediction : Set where

ckmVcbCarrierPredictionImpossibleHere :
  CKMVcbCarrierPrediction →
  ⊥
ckmVcbCarrierPredictionImpossibleHere ()

pdgAInputLabel : String
pdgAInputLabel =
  "A = 0.8086 is PDG input from the Wolfenstein parametrisation"

wolfensteinVcbIdentityLabel : String
wolfensteinVcbIdentityLabel =
  "|Vcb| = A*lambda^2 is a tautological identity within the Wolfenstein parametrisation"

noCarrierADerivationLabel : String
noCarrierADerivationLabel =
  "No receipt derives A = 0.8086 from carrier arithmetic"

canonicalCKMVcbDemotionCorrections :
  List String
canonicalCKMVcbDemotionCorrections =
  "CKMFullHonestyReceipt:154"
  ∷ "Paper6DraftCompleteReceipt:178"
  ∷ []

canonicalCKMVcbDemotionBoundary :
  List String
canonicalCKMVcbDemotionBoundary =
  pdgAInputLabel
  ∷ wolfensteinVcbIdentityLabel
  ∷ noCarrierADerivationLabel
  ∷ "Therefore |Vcb| is demoted from carrier prediction to PDG-tautology status"
  ∷ []

record CKMVcbDemotionReceipt : Set where
  field
    vcbStatus :
      CKMVcbStatus

    vcbStatusIsPDGTautology :
      vcbStatus ≡ pdgTautology

    wolfensteinAValue :
      Float

    wolfensteinAValueIsPDGInput :
      wolfensteinAValue ≡ 0.8086

    wolfensteinAInputLabel :
      String

    wolfensteinAInputLabelIsCanonical :
      wolfensteinAInputLabel ≡ pdgAInputLabel

    vcbFormula :
      String

    vcbFormulaIsWolfensteinIdentity :
      vcbFormula ≡ wolfensteinVcbIdentityLabel

    wolfensteinParametrisationIdentity :
      Bool

    wolfensteinParametrisationIdentityIsTrue :
      wolfensteinParametrisationIdentity ≡ true

    independentCarrierPrediction :
      Bool

    independentCarrierPredictionIsFalse :
      independentCarrierPrediction ≡ false

    notACarrierPrediction :
      Bool

    notACarrierPredictionIsTrue :
      notACarrierPrediction ≡ true

    carrierDerivesA :
      Bool

    carrierDerivesAIsFalse :
      carrierDerivesA ≡ false

    noReceiptDerivesAFromCarrierArithmetic :
      Bool

    noReceiptDerivesAFromCarrierArithmeticIsTrue :
      noReceiptDerivesAFromCarrierArithmetic ≡ true

    noCarrierADerivation :
      String

    noCarrierADerivationIsCanonical :
      noCarrierADerivation ≡ noCarrierADerivationLabel

    corrects :
      List String

    correctsAreCanonical :
      corrects ≡ canonicalCKMVcbDemotionCorrections

    blockers :
      List CKMVcbDemotionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCKMVcbDemotionBlockers

    carrierPredictionFlags :
      List CKMVcbCarrierPrediction

    carrierPredictionFlagsAreEmpty :
      carrierPredictionFlags ≡ []

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalCKMVcbDemotionBoundary

open CKMVcbDemotionReceipt public

canonicalCKMVcbDemotionReceipt :
  CKMVcbDemotionReceipt
canonicalCKMVcbDemotionReceipt =
  record
    { vcbStatus =
        pdgTautology
    ; vcbStatusIsPDGTautology =
        refl
    ; wolfensteinAValue =
        0.8086
    ; wolfensteinAValueIsPDGInput =
        refl
    ; wolfensteinAInputLabel =
        pdgAInputLabel
    ; wolfensteinAInputLabelIsCanonical =
        refl
    ; vcbFormula =
        wolfensteinVcbIdentityLabel
    ; vcbFormulaIsWolfensteinIdentity =
        refl
    ; wolfensteinParametrisationIdentity =
        true
    ; wolfensteinParametrisationIdentityIsTrue =
        refl
    ; independentCarrierPrediction =
        false
    ; independentCarrierPredictionIsFalse =
        refl
    ; notACarrierPrediction =
        true
    ; notACarrierPredictionIsTrue =
        refl
    ; carrierDerivesA =
        false
    ; carrierDerivesAIsFalse =
        refl
    ; noReceiptDerivesAFromCarrierArithmetic =
        true
    ; noReceiptDerivesAFromCarrierArithmeticIsTrue =
        refl
    ; noCarrierADerivation =
        noCarrierADerivationLabel
    ; noCarrierADerivationIsCanonical =
        refl
    ; corrects =
        canonicalCKMVcbDemotionCorrections
    ; correctsAreCanonical =
        refl
    ; blockers =
        canonicalCKMVcbDemotionBlockers
    ; blockersAreCanonical =
        refl
    ; carrierPredictionFlags =
        []
    ; carrierPredictionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        canonicalCKMVcbDemotionBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

ckmVcbStatusIsPDGTautology :
  vcbStatus canonicalCKMVcbDemotionReceipt ≡ pdgTautology
ckmVcbStatusIsPDGTautology =
  refl

ckmVcbNotACarrierPrediction :
  notACarrierPrediction canonicalCKMVcbDemotionReceipt ≡ true
ckmVcbNotACarrierPrediction =
  refl

ckmVcbDoesNotDeriveAFromCarrier :
  carrierDerivesA canonicalCKMVcbDemotionReceipt ≡ false
ckmVcbDoesNotDeriveAFromCarrier =
  refl

ckmVcbCorrectionsAreCanonical :
  corrects canonicalCKMVcbDemotionReceipt
  ≡
  canonicalCKMVcbDemotionCorrections
ckmVcbCorrectionsAreCanonical =
  refl
