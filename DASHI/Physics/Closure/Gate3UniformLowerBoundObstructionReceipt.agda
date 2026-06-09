module DASHI.Physics.Closure.Gate3UniformLowerBoundObstructionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Gate3FiniteCutoffFrameLowerBoundProofReceipt
  as Finite
import DASHI.Physics.Closure.Gate3NormDictionaryReceipt as Norm

------------------------------------------------------------------------
-- Gate 3 uniform lower-bound obstruction receipt.
--
-- This receipt records why the finite-cutoff frame receipt cannot be read
-- as a uniform infinite-H lower frame bound.  The obstruction is represented
-- explicitly as closed data and Bool evidence: finite A_N > 0 is available,
-- but uniformity in N and continuum promotion are absent.

data Gate3UniformLowerBoundObstructionStatus : Set where
  finiteCutoffDoesNotYieldUniformInfiniteBound_failClosed :
    Gate3UniformLowerBoundObstructionStatus

data Gate3UniformLowerBoundBlocker : Set where
  lowerBoundDependsOnCutoff :
    Gate3UniformLowerBoundBlocker

  noPositiveInfimumOverCutoffs :
    Gate3UniformLowerBoundBlocker

  noTightnessOrCompactnessUpgradeHere :
    Gate3UniformLowerBoundBlocker

  noAdelicSobolevNormBindingUpgradeHere :
    Gate3UniformLowerBoundBlocker

  noSig15CoherenceUpgradeHere :
    Gate3UniformLowerBoundBlocker

canonicalGate3UniformLowerBoundBlockers :
  List Gate3UniformLowerBoundBlocker
canonicalGate3UniformLowerBoundBlockers =
  lowerBoundDependsOnCutoff
  ∷ noPositiveInfimumOverCutoffs
  ∷ noTightnessOrCompactnessUpgradeHere
  ∷ noAdelicSobolevNormBindingUpgradeHere
  ∷ noSig15CoherenceUpgradeHere
  ∷ []

data Gate3UniformLowerBoundNonClaim : Set where
  noUniformAOnInfiniteH :
    Gate3UniformLowerBoundNonClaim

  noContinuumFrameBound :
    Gate3UniformLowerBoundNonClaim

  noGate3Closure :
    Gate3UniformLowerBoundNonClaim

  noYangMillsMassGap :
    Gate3UniformLowerBoundNonClaim

  noClayPromotion :
    Gate3UniformLowerBoundNonClaim

canonicalGate3UniformLowerBoundNonClaims :
  List Gate3UniformLowerBoundNonClaim
canonicalGate3UniformLowerBoundNonClaims =
  noUniformAOnInfiniteH
  ∷ noContinuumFrameBound
  ∷ noGate3Closure
  ∷ noYangMillsMassGap
  ∷ noClayPromotion
  ∷ []

data Gate3UniformLowerBoundPromotion : Set where

gate3UniformLowerBoundPromotionImpossibleHere :
  Gate3UniformLowerBoundPromotion →
  ⊥
gate3UniformLowerBoundPromotionImpossibleHere ()

uniformLowerBoundObstructionStatement :
  String
uniformLowerBoundObstructionStatement =
  "Gate3 uniform lower-bound obstruction: finite cutoff evidence A_N > 0 does not supply a cutoff-independent A > 0 on infinite H; the uniform infimum, compactness/tightness upgrade, norm binding, and Sig15 coherence remain open."

record Gate3UniformLowerBoundObstructionReceipt : Setω where
  field
    status :
      Gate3UniformLowerBoundObstructionStatus

    statusIsFailClosed :
      status
      ≡
      finiteCutoffDoesNotYieldUniformInfiniteBound_failClosed

    finiteCutoffReceipt :
      Finite.Gate3FiniteCutoffFrameLowerBoundProofReceipt

    finiteCutoffBoundRecorded :
      Finite.finiteLowerBoundANPositiveRecorded finiteCutoffReceipt
      ≡
      true

    finiteCutoffNotUniform :
      Finite.finiteLowerBoundANUniformInN finiteCutoffReceipt
      ≡
      false

    finiteCutoffNoAnalyticUniformLimit :
      Finite.analyticUniformLimitExtracted finiteCutoffReceipt
      ≡
      false

    finiteCutoffNoContinuumGate3 :
      Finite.continuumGate3Promoted finiteCutoffReceipt
      ≡
      false

    normDictionaryReceipt :
      Norm.Gate3NormDictionaryReceipt

    normDictionaryReceiptIsCanonical :
      normDictionaryReceipt ≡ Norm.canonicalGate3NormDictionaryReceipt

    normDictionaryFiniteCutoffRecorded :
      Norm.finiteCutoffHNFrameBoundANPositiveRecorded
        normDictionaryReceipt
      ≡
      true

    normDictionaryUniformInfiniteBoundStillFalse :
      Norm.uniformInfiniteHLowerFrameBoundAProved normDictionaryReceipt
      ≡
      false

    normDictionaryNormBindingsStillFalse :
      Norm.normBindingsProved normDictionaryReceipt ≡ false

    normDictionarySig15CoherenceStillFalse :
      Norm.sig15StableCoherenceProved normDictionaryReceipt ≡ false

    normDictionaryContinuumGate3StillFalse :
      Norm.continuumGate3Promoted normDictionaryReceipt ≡ false

    finiteANPositive :
      Bool

    finiteANPositiveIsTrue :
      finiteANPositive ≡ true

    uniformAOnInfiniteH :
      Bool

    uniformAOnInfiniteHIsFalse :
      uniformAOnInfiniteH ≡ false

    positiveInfimumOverCutoffsProved :
      Bool

    positiveInfimumOverCutoffsProvedIsFalse :
      positiveInfimumOverCutoffsProved ≡ false

    compactnessTightnessUpgradeProved :
      Bool

    compactnessTightnessUpgradeProvedIsFalse :
      compactnessTightnessUpgradeProved ≡ false

    continuumGate3Promoted :
      Bool

    continuumGate3PromotedIsFalse :
      continuumGate3Promoted ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    blockers :
      List Gate3UniformLowerBoundBlocker

    blockersAreCanonical :
      blockers ≡ canonicalGate3UniformLowerBoundBlockers

    nonClaims :
      List Gate3UniformLowerBoundNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalGate3UniformLowerBoundNonClaims

    statement :
      String

    statementIsCanonical :
      statement ≡ uniformLowerBoundObstructionStatement

    promotions :
      List Gate3UniformLowerBoundPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      Gate3UniformLowerBoundPromotion →
      ⊥

open Gate3UniformLowerBoundObstructionReceipt public

canonicalGate3UniformLowerBoundObstructionReceipt :
  Gate3UniformLowerBoundObstructionReceipt
canonicalGate3UniformLowerBoundObstructionReceipt =
  record
    { status =
        finiteCutoffDoesNotYieldUniformInfiniteBound_failClosed
    ; statusIsFailClosed =
        refl
    ; finiteCutoffReceipt =
        Finite.canonicalGate3FiniteCutoffFrameLowerBoundProofReceipt
    ; finiteCutoffBoundRecorded =
        refl
    ; finiteCutoffNotUniform =
        refl
    ; finiteCutoffNoAnalyticUniformLimit =
        refl
    ; finiteCutoffNoContinuumGate3 =
        refl
    ; normDictionaryReceipt =
        Norm.canonicalGate3NormDictionaryReceipt
    ; normDictionaryReceiptIsCanonical =
        refl
    ; normDictionaryFiniteCutoffRecorded =
        refl
    ; normDictionaryUniformInfiniteBoundStillFalse =
        refl
    ; normDictionaryNormBindingsStillFalse =
        refl
    ; normDictionarySig15CoherenceStillFalse =
        refl
    ; normDictionaryContinuumGate3StillFalse =
        refl
    ; finiteANPositive =
        true
    ; finiteANPositiveIsTrue =
        refl
    ; uniformAOnInfiniteH =
        false
    ; uniformAOnInfiniteHIsFalse =
        refl
    ; positiveInfimumOverCutoffsProved =
        false
    ; positiveInfimumOverCutoffsProvedIsFalse =
        refl
    ; compactnessTightnessUpgradeProved =
        false
    ; compactnessTightnessUpgradeProvedIsFalse =
        refl
    ; continuumGate3Promoted =
        false
    ; continuumGate3PromotedIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; blockers =
        canonicalGate3UniformLowerBoundBlockers
    ; blockersAreCanonical =
        refl
    ; nonClaims =
        canonicalGate3UniformLowerBoundNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; statement =
        uniformLowerBoundObstructionStatement
    ; statementIsCanonical =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        gate3UniformLowerBoundPromotionImpossibleHere
    }

canonicalGate3UniformLowerBoundFiniteOnly :
  finiteANPositive canonicalGate3UniformLowerBoundObstructionReceipt
  ≡
  true
canonicalGate3UniformLowerBoundFiniteOnly =
  refl

canonicalGate3UniformLowerBoundNotUniform :
  uniformAOnInfiniteH canonicalGate3UniformLowerBoundObstructionReceipt
  ≡
  false
canonicalGate3UniformLowerBoundNotUniform =
  refl

canonicalGate3UniformLowerBoundNoGate3Promotion :
  continuumGate3Promoted canonicalGate3UniformLowerBoundObstructionReceipt
  ≡
  false
canonicalGate3UniformLowerBoundNoGate3Promotion =
  refl
