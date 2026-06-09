module DASHI.Physics.Closure.Gate3FiniteCutoffFrameLowerBoundProofReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Gate3NormDictionaryReceipt as Norm

------------------------------------------------------------------------
-- Gate 3 finite-cutoff frame lower-bound receipt.
--
-- This receipt records the finite-dimensional frame fact used by Gate 3:
-- at a fixed finite cutoff H_N, a positive lower frame bound A_N may be
-- carried as finite evidence.  It deliberately does not promote a uniform
-- infinite-H lower frame bound, norm-binding theorem, continuum Gate 3
-- closure, or Clay result.

data Gate3FiniteCutoffFrameLowerBoundStatus : Set where
  finiteCutoffFrameLowerBoundRecorded_failClosed :
    Gate3FiniteCutoffFrameLowerBoundStatus

data Gate3FiniteCutoffFrameIngredient : Set where
  finiteCutoffCarrierH_N :
    Gate3FiniteCutoffFrameIngredient

  finiteFrameFamilyOnH_N :
    Gate3FiniteCutoffFrameIngredient

  finiteGramMatrixOnH_N :
    Gate3FiniteCutoffFrameIngredient

  positiveFiniteLowerBoundA_N :
    Gate3FiniteCutoffFrameIngredient

canonicalGate3FiniteCutoffFrameIngredients :
  List Gate3FiniteCutoffFrameIngredient
canonicalGate3FiniteCutoffFrameIngredients =
  finiteCutoffCarrierH_N
  ∷ finiteFrameFamilyOnH_N
  ∷ finiteGramMatrixOnH_N
  ∷ positiveFiniteLowerBoundA_N
  ∷ []

data Gate3FiniteCutoffFrameBoundary : Set where
  boundDependsOnCutoffN :
    Gate3FiniteCutoffFrameBoundary

  noUniformInfiniteHLowerBoundExtracted :
    Gate3FiniteCutoffFrameBoundary

  noAdelicSobolevNormBindingProved :
    Gate3FiniteCutoffFrameBoundary

  noSig15StableCoherenceProved :
    Gate3FiniteCutoffFrameBoundary

  noContinuumGate3Closure :
    Gate3FiniteCutoffFrameBoundary

canonicalGate3FiniteCutoffFrameBoundaries :
  List Gate3FiniteCutoffFrameBoundary
canonicalGate3FiniteCutoffFrameBoundaries =
  boundDependsOnCutoffN
  ∷ noUniformInfiniteHLowerBoundExtracted
  ∷ noAdelicSobolevNormBindingProved
  ∷ noSig15StableCoherenceProved
  ∷ noContinuumGate3Closure
  ∷ []

data Gate3FiniteCutoffFramePromotion : Set where

gate3FiniteCutoffFramePromotionImpossibleHere :
  Gate3FiniteCutoffFramePromotion →
  ⊥
gate3FiniteCutoffFramePromotionImpossibleHere ()

finiteCutoffFrameReceiptStatement :
  String
finiteCutoffFrameReceiptStatement =
  "Gate3 finite-cutoff frame receipt: for each selected finite cutoff H_N, the lower frame bound A_N > 0 is recorded as finite evidence only; it is not a uniform lower frame bound on infinite H."

record Gate3FiniteCutoffFrameLowerBoundProofReceipt : Setω where
  field
    status :
      Gate3FiniteCutoffFrameLowerBoundStatus

    statusIsFailClosed :
      status ≡ finiteCutoffFrameLowerBoundRecorded_failClosed

    normDictionaryReceipt :
      Norm.Gate3NormDictionaryReceipt

    normDictionaryFiniteCutoffRecorded :
      Norm.finiteCutoffHNFrameBoundANPositiveRecorded
        normDictionaryReceipt
      ≡
      true

    normDictionaryNoUniformInfiniteBound :
      Norm.uniformInfiniteHLowerFrameBoundAProved normDictionaryReceipt
      ≡
      false

    normDictionaryNoContinuumGate3Promotion :
      Norm.continuumGate3Promoted normDictionaryReceipt
      ≡
      false

    cutoffLevel :
      Nat

    cutoffLevelIsConcrete :
      cutoffLevel ≡ suc zero

    finiteCutoffSelected :
      Bool

    finiteCutoffSelectedIsTrue :
      finiteCutoffSelected ≡ true

    finiteCarrierDimensionRecorded :
      Bool

    finiteCarrierDimensionRecordedIsTrue :
      finiteCarrierDimensionRecorded ≡ true

    finiteFrameFamilyRecorded :
      Bool

    finiteFrameFamilyRecordedIsTrue :
      finiteFrameFamilyRecorded ≡ true

    finiteGramMatrixRecorded :
      Bool

    finiteGramMatrixRecordedIsTrue :
      finiteGramMatrixRecorded ≡ true

    finiteLowerBoundANPositiveRecorded :
      Bool

    finiteLowerBoundANPositiveRecordedIsTrue :
      finiteLowerBoundANPositiveRecorded ≡ true

    finiteLowerBoundANUniformInN :
      Bool

    finiteLowerBoundANUniformInNIsFalse :
      finiteLowerBoundANUniformInN ≡ false

    analyticUniformLimitExtracted :
      Bool

    analyticUniformLimitExtractedIsFalse :
      analyticUniformLimitExtracted ≡ false

    continuumGate3Promoted :
      Bool

    continuumGate3PromotedIsFalse :
      continuumGate3Promoted ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    ingredients :
      List Gate3FiniteCutoffFrameIngredient

    ingredientsAreCanonical :
      ingredients ≡ canonicalGate3FiniteCutoffFrameIngredients

    boundaries :
      List Gate3FiniteCutoffFrameBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalGate3FiniteCutoffFrameBoundaries

    statement :
      String

    statementIsCanonical :
      statement ≡ finiteCutoffFrameReceiptStatement

    promotions :
      List Gate3FiniteCutoffFramePromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      Gate3FiniteCutoffFramePromotion →
      ⊥

open Gate3FiniteCutoffFrameLowerBoundProofReceipt public

canonicalGate3FiniteCutoffFrameLowerBoundProofReceipt :
  Gate3FiniteCutoffFrameLowerBoundProofReceipt
canonicalGate3FiniteCutoffFrameLowerBoundProofReceipt =
  record
    { status =
        finiteCutoffFrameLowerBoundRecorded_failClosed
    ; statusIsFailClosed =
        refl
    ; normDictionaryReceipt =
        Norm.canonicalGate3NormDictionaryReceipt
    ; normDictionaryFiniteCutoffRecorded =
        refl
    ; normDictionaryNoUniformInfiniteBound =
        refl
    ; normDictionaryNoContinuumGate3Promotion =
        refl
    ; cutoffLevel =
        suc zero
    ; cutoffLevelIsConcrete =
        refl
    ; finiteCutoffSelected =
        true
    ; finiteCutoffSelectedIsTrue =
        refl
    ; finiteCarrierDimensionRecorded =
        true
    ; finiteCarrierDimensionRecordedIsTrue =
        refl
    ; finiteFrameFamilyRecorded =
        true
    ; finiteFrameFamilyRecordedIsTrue =
        refl
    ; finiteGramMatrixRecorded =
        true
    ; finiteGramMatrixRecordedIsTrue =
        refl
    ; finiteLowerBoundANPositiveRecorded =
        true
    ; finiteLowerBoundANPositiveRecordedIsTrue =
        refl
    ; finiteLowerBoundANUniformInN =
        false
    ; finiteLowerBoundANUniformInNIsFalse =
        refl
    ; analyticUniformLimitExtracted =
        false
    ; analyticUniformLimitExtractedIsFalse =
        refl
    ; continuumGate3Promoted =
        false
    ; continuumGate3PromotedIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; ingredients =
        canonicalGate3FiniteCutoffFrameIngredients
    ; ingredientsAreCanonical =
        refl
    ; boundaries =
        canonicalGate3FiniteCutoffFrameBoundaries
    ; boundariesAreCanonical =
        refl
    ; statement =
        finiteCutoffFrameReceiptStatement
    ; statementIsCanonical =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        gate3FiniteCutoffFramePromotionImpossibleHere
    }

canonicalGate3FiniteCutoffFrameBoundRecorded :
  finiteLowerBoundANPositiveRecorded
    canonicalGate3FiniteCutoffFrameLowerBoundProofReceipt
  ≡
  true
canonicalGate3FiniteCutoffFrameBoundRecorded =
  refl

canonicalGate3FiniteCutoffFrameNoUniformBound :
  finiteLowerBoundANUniformInN
    canonicalGate3FiniteCutoffFrameLowerBoundProofReceipt
  ≡
  false
canonicalGate3FiniteCutoffFrameNoUniformBound =
  refl

canonicalGate3FiniteCutoffFrameNoContinuumGate3 :
  continuumGate3Promoted
    canonicalGate3FiniteCutoffFrameLowerBoundProofReceipt
  ≡
  false
canonicalGate3FiniteCutoffFrameNoContinuumGate3 =
  refl
