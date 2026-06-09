module DASHI.Physics.Closure.Gate3GershgorinFiniteFrameBoundReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Gate3FiniteCutoffFrameLowerBoundProofReceipt
  as Finite
import DASHI.Physics.Closure.Gate3UniformLowerBoundObstructionReceipt
  as Uniform

------------------------------------------------------------------------
-- Gate 3 Gershgorin finite frame bound receipt.
--
-- This receipt records the finite cutoff route for a positive lower frame
-- bound.  The condition is conditional on normalized atoms, a finite maximal
-- cross term mu_N, and the strict row-sum inequality
--
--   (N - 1) * mu_N < 1.
--
-- Under those finite assumptions the Gershgorin lower estimate is
--
--   A_N >= 1 - (N - 1) * mu_N > 0.
--
-- Phase completeness by itself is not recorded as sufficient for A_N > 0.
-- No cutoff-uniform lower bound, continuum Gate 3 claim, or Clay claim follows.

data Gate3GershgorinFiniteFrameBoundStatus : Set where
  gershgorinFiniteFrameBoundRecorded_conditional_failClosed :
    Gate3GershgorinFiniteFrameBoundStatus

data GershgorinFiniteFrameCondition : Set where
  normalizedAtoms :
    GershgorinFiniteFrameCondition

  finiteMaxCrossTermMu_N :
    GershgorinFiniteFrameCondition

  strictGershgorinRowSum :
    GershgorinFiniteFrameCondition

canonicalGershgorinFiniteFrameConditions :
  List GershgorinFiniteFrameCondition
canonicalGershgorinFiniteFrameConditions =
  normalizedAtoms
  ∷ finiteMaxCrossTermMu_N
  ∷ strictGershgorinRowSum
  ∷ []

data GershgorinFiniteFrameNonClaim : Set where
  noPhaseCompletenessAloneToA_N :
    GershgorinFiniteFrameNonClaim

  noCutoffUniformLowerBound :
    GershgorinFiniteFrameNonClaim

  noContinuumGate3Claim :
    GershgorinFiniteFrameNonClaim

  noClayClaim :
    GershgorinFiniteFrameNonClaim

canonicalGershgorinFiniteFrameNonClaims :
  List GershgorinFiniteFrameNonClaim
canonicalGershgorinFiniteFrameNonClaims =
  noPhaseCompletenessAloneToA_N
  ∷ noCutoffUniformLowerBound
  ∷ noContinuumGate3Claim
  ∷ noClayClaim
  ∷ []

data Gate3GershgorinFiniteFramePromotion : Set where

gate3GershgorinFiniteFramePromotionImpossibleHere :
  Gate3GershgorinFiniteFramePromotion →
  ⊥
gate3GershgorinFiniteFramePromotionImpossibleHere ()

canonicalCutoffN :
  Nat
canonicalCutoffN =
  3

canonicalMu_N_Milli :
  Nat
canonicalMu_N_Milli =
  400

canonicalRowSumMilli :
  Nat
canonicalRowSumMilli =
  800

canonicalOneMilli :
  Nat
canonicalOneMilli =
  1000

canonicalLowerBoundMilli :
  Nat
canonicalLowerBoundMilli =
  200

gershgorinFiniteConditionStatement :
  String
gershgorinFiniteConditionStatement =
  "Finite cutoff condition: normalized atoms plus max cross term mu_N plus (N-1)*mu_N < 1 gives A_N >= 1-(N-1)*mu_N > 0."

phaseCompletenessBoundaryStatement :
  String
phaseCompletenessBoundaryStatement =
  "Phase completeness alone does not imply A_N > 0; the strict Gershgorin row-sum condition is required."

uniformSeparationBoundaryStatement :
  String
uniformSeparationBoundaryStatement =
  "The Gershgorin estimate is finite-cutoff only and does not supply a cutoff-uniform separation bound."

record Gate3GershgorinFiniteFrameBoundReceipt : Setω where
  field
    status :
      Gate3GershgorinFiniteFrameBoundStatus

    statusIsFailClosed :
      status
      ≡
      gershgorinFiniteFrameBoundRecorded_conditional_failClosed

    finiteCutoffReceipt :
      Finite.Gate3FiniteCutoffFrameLowerBoundProofReceipt

    finiteCutoffSelected :
      Finite.finiteCutoffSelected finiteCutoffReceipt ≡ true

    uniformObstructionReceipt :
      Uniform.Gate3UniformLowerBoundObstructionReceipt

    uniformAOnInfiniteHStillFalse :
      Uniform.uniformAOnInfiniteH uniformObstructionReceipt ≡ false

    cutoffN :
      Nat

    cutoffNIsCanonical :
      cutoffN ≡ canonicalCutoffN

    mu_N_Milli :
      Nat

    mu_N_MilliIsCanonical :
      mu_N_Milli ≡ canonicalMu_N_Milli

    rowSumMilli :
      Nat

    rowSumMilliIsCanonical :
      rowSumMilli ≡ canonicalRowSumMilli

    oneMilli :
      Nat

    oneMilliIsCanonical :
      oneMilli ≡ canonicalOneMilli

    lowerBoundMilli :
      Nat

    lowerBoundMilliIsCanonical :
      lowerBoundMilli ≡ canonicalLowerBoundMilli

    atomsNormalized :
      Bool

    atomsNormalizedIsTrue :
      atomsNormalized ≡ true

    maxCrossTermRecorded :
      Bool

    maxCrossTermRecordedIsTrue :
      maxCrossTermRecorded ≡ true

    rowSumStrictlyBelowOne :
      Bool

    rowSumStrictlyBelowOneIsTrue :
      rowSumStrictlyBelowOne ≡ true

    finiteLowerBoundConditional :
      Bool

    finiteLowerBoundConditionalIsTrue :
      finiteLowerBoundConditional ≡ true

    gershgorinLowerEstimateRecorded :
      Bool

    gershgorinLowerEstimateRecordedIsTrue :
      gershgorinLowerEstimateRecorded ≡ true

    phaseCompletenessAloneImpliesA_NPositive :
      Bool

    phaseCompletenessAloneImpliesA_NPositiveIsFalse :
      phaseCompletenessAloneImpliesA_NPositive ≡ false

    uniformSeparationObtained :
      Bool

    uniformSeparationObtainedIsFalse :
      uniformSeparationObtained ≡ false

    continuumGate3Promoted :
      Bool

    continuumGate3PromotedIsFalse :
      continuumGate3Promoted ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    conditions :
      List GershgorinFiniteFrameCondition

    conditionsAreCanonical :
      conditions ≡ canonicalGershgorinFiniteFrameConditions

    nonClaims :
      List GershgorinFiniteFrameNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalGershgorinFiniteFrameNonClaims

    finiteConditionBoundary :
      String

    finiteConditionBoundaryIsCanonical :
      finiteConditionBoundary ≡ gershgorinFiniteConditionStatement

    phaseCompletenessBoundary :
      String

    phaseCompletenessBoundaryIsCanonical :
      phaseCompletenessBoundary ≡ phaseCompletenessBoundaryStatement

    uniformSeparationBoundary :
      String

    uniformSeparationBoundaryIsCanonical :
      uniformSeparationBoundary ≡ uniformSeparationBoundaryStatement

    promotions :
      List Gate3GershgorinFiniteFramePromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      Gate3GershgorinFiniteFramePromotion →
      ⊥

open Gate3GershgorinFiniteFrameBoundReceipt public

canonicalGate3GershgorinFiniteFrameBoundReceipt :
  Gate3GershgorinFiniteFrameBoundReceipt
canonicalGate3GershgorinFiniteFrameBoundReceipt =
  record
    { status =
        gershgorinFiniteFrameBoundRecorded_conditional_failClosed
    ; statusIsFailClosed =
        refl
    ; finiteCutoffReceipt =
        Finite.canonicalGate3FiniteCutoffFrameLowerBoundProofReceipt
    ; finiteCutoffSelected =
        refl
    ; uniformObstructionReceipt =
        Uniform.canonicalGate3UniformLowerBoundObstructionReceipt
    ; uniformAOnInfiniteHStillFalse =
        refl
    ; cutoffN =
        canonicalCutoffN
    ; cutoffNIsCanonical =
        refl
    ; mu_N_Milli =
        canonicalMu_N_Milli
    ; mu_N_MilliIsCanonical =
        refl
    ; rowSumMilli =
        canonicalRowSumMilli
    ; rowSumMilliIsCanonical =
        refl
    ; oneMilli =
        canonicalOneMilli
    ; oneMilliIsCanonical =
        refl
    ; lowerBoundMilli =
        canonicalLowerBoundMilli
    ; lowerBoundMilliIsCanonical =
        refl
    ; atomsNormalized =
        true
    ; atomsNormalizedIsTrue =
        refl
    ; maxCrossTermRecorded =
        true
    ; maxCrossTermRecordedIsTrue =
        refl
    ; rowSumStrictlyBelowOne =
        true
    ; rowSumStrictlyBelowOneIsTrue =
        refl
    ; finiteLowerBoundConditional =
        true
    ; finiteLowerBoundConditionalIsTrue =
        refl
    ; gershgorinLowerEstimateRecorded =
        true
    ; gershgorinLowerEstimateRecordedIsTrue =
        refl
    ; phaseCompletenessAloneImpliesA_NPositive =
        false
    ; phaseCompletenessAloneImpliesA_NPositiveIsFalse =
        refl
    ; uniformSeparationObtained =
        false
    ; uniformSeparationObtainedIsFalse =
        refl
    ; continuumGate3Promoted =
        false
    ; continuumGate3PromotedIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; conditions =
        canonicalGershgorinFiniteFrameConditions
    ; conditionsAreCanonical =
        refl
    ; nonClaims =
        canonicalGershgorinFiniteFrameNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; finiteConditionBoundary =
        gershgorinFiniteConditionStatement
    ; finiteConditionBoundaryIsCanonical =
        refl
    ; phaseCompletenessBoundary =
        phaseCompletenessBoundaryStatement
    ; phaseCompletenessBoundaryIsCanonical =
        refl
    ; uniformSeparationBoundary =
        uniformSeparationBoundaryStatement
    ; uniformSeparationBoundaryIsCanonical =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        gate3GershgorinFiniteFramePromotionImpossibleHere
    }

canonicalGate3GershgorinFiniteFrameConditional :
  finiteLowerBoundConditional canonicalGate3GershgorinFiniteFrameBoundReceipt
  ≡
  true
canonicalGate3GershgorinFiniteFrameConditional =
  refl

canonicalGate3GershgorinPhaseCompletenessAloneFalse :
  phaseCompletenessAloneImpliesA_NPositive
    canonicalGate3GershgorinFiniteFrameBoundReceipt
  ≡
  false
canonicalGate3GershgorinPhaseCompletenessAloneFalse =
  refl

canonicalGate3GershgorinNoUniformSeparation :
  uniformSeparationObtained canonicalGate3GershgorinFiniteFrameBoundReceipt
  ≡
  false
canonicalGate3GershgorinNoUniformSeparation =
  refl
