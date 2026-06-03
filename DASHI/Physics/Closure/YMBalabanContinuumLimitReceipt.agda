module DASHI.Physics.Closure.YMBalabanContinuumLimitReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMFortyThreeStepBalabanTargetReceipt
  as FortyThree

------------------------------------------------------------------------
-- YM Balaban continuum-limit correction.
--
-- Sprint 5 YM receipt.  It retracts the finite-step induction reading of
-- the 43-step diagnostic and replaces it with the uniform continuum-limit
-- Balaban target.

data YMBalabanContinuumLimitStatus : Set where
  ymBalabanContinuumLimitRecorded_noPromotion :
    YMBalabanContinuumLimitStatus

data YMBalabanContinuumTarget : Set where
  finiteFortyThreeStepInductionRetracted :
    YMBalabanContinuumTarget

  oneLoopCrossingInformationalOnly :
    YMBalabanContinuumTarget

  continuumLimitUniformBalaban :
    YMBalabanContinuumTarget

  rhoUniformAsAZeroTendsToZero :
    YMBalabanContinuumTarget

  existsScaleCrossingForEachCutoff :
    YMBalabanContinuumTarget

canonicalYMBalabanContinuumTargets :
  List YMBalabanContinuumTarget
canonicalYMBalabanContinuumTargets =
  finiteFortyThreeStepInductionRetracted
  ∷ oneLoopCrossingInformationalOnly
  ∷ continuumLimitUniformBalaban
  ∷ rhoUniformAsAZeroTendsToZero
  ∷ existsScaleCrossingForEachCutoff
  ∷ []

data YMBalabanContinuumNonClaim : Set where
  oneLoopRunningIsNotBalabanProof :
    YMBalabanContinuumNonClaim

  qAtBetaPhysExpandsSoInductionCannotStart :
    YMBalabanContinuumNonClaim

  finiteStepDiagnosticIsNotContinuumUniformity :
    YMBalabanContinuumNonClaim

  noClayPromotion :
    YMBalabanContinuumNonClaim

canonicalYMBalabanContinuumNonClaims :
  List YMBalabanContinuumNonClaim
canonicalYMBalabanContinuumNonClaims =
  oneLoopRunningIsNotBalabanProof
  ∷ qAtBetaPhysExpandsSoInductionCannotStart
  ∷ finiteStepDiagnosticIsNotContinuumUniformity
  ∷ noClayPromotion
  ∷ []

data YMBalabanContinuumLimitPromotion : Set where

ymBalabanContinuumLimitPromotionImpossibleHere :
  YMBalabanContinuumLimitPromotion →
  ⊥
ymBalabanContinuumLimitPromotionImpossibleHere ()

qAtBetaPhysHundredths : Nat
qAtBetaPhysHundredths =
  453

oneLoopKEstimateTenths : Nat
oneLoopKEstimateTenths =
  422

betaStrictMillionths : Nat
betaStrictMillionths =
  13631603

ymBalabanContinuumTargetText : String
ymBalabanContinuumTargetText =
  "YMBalabanContinuumLimit: for every sufficiently small initial cutoff a0, find k(a0) with beta_eff(a_k)>beta_strict and rho_k<1 uniformly as a0->0."

ymBalabanContinuumBoundaryText : String
ymBalabanContinuumBoundaryText =
  "This receipt retracts the finite 43-step induction interpretation. It records the corrected continuum-uniform Balaban target only; it does not prove nonperturbative RG transfer, continuum YM, OS/Wightman, mass gap, or Clay YM."

record YMBalabanContinuumLimitReceipt : Setω where
  field
    status :
      YMBalabanContinuumLimitStatus

    statusIsCanonical :
      status ≡ ymBalabanContinuumLimitRecorded_noPromotion

    fortyThreeReceipt :
      FortyThree.YMFortyThreeStepBalabanTargetReceipt

    previousFortyThreeStillOpen :
      FortyThree.nonperturbativeBalabanTransferProved fortyThreeReceipt
      ≡
      false

    previousClayStillFalse :
      FortyThree.clayYangMillsPromoted fortyThreeReceipt ≡ false

    targets :
      List YMBalabanContinuumTarget

    targetsAreCanonical :
      targets ≡ canonicalYMBalabanContinuumTargets

    nonClaims :
      List YMBalabanContinuumNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalYMBalabanContinuumNonClaims

    fortyThreeStepFiniteTargetRetracted :
      Bool

    fortyThreeStepFiniteTargetRetractedIsTrue :
      fortyThreeStepFiniteTargetRetracted ≡ true

    finiteInductionMisconceived :
      Bool

    finiteInductionMisconceivedIsTrue :
      finiteInductionMisconceived ≡ true

    qAtBetaPhys6 :
      Nat

    qAtBetaPhys6Is453 :
      qAtBetaPhys6 ≡ qAtBetaPhysHundredths

    qAtBetaPhys6Expands :
      Bool

    qAtBetaPhys6ExpandsIsTrue :
      qAtBetaPhys6Expands ≡ true

    oneLoopKEstimate :
      Nat

    oneLoopKEstimateIs422 :
      oneLoopKEstimate ≡ oneLoopKEstimateTenths

    betaStrict :
      Nat

    betaStrictIs13631603 :
      betaStrict ≡ betaStrictMillionths

    oneLoopEstimateInformationalOnly :
      Bool

    oneLoopEstimateInformationalOnlyIsTrue :
      oneLoopEstimateInformationalOnly ≡ true

    continuumLimitUniformBalabanTarget :
      Set

    continuumLimitUniformBalabanProved :
      Bool

    continuumLimitUniformBalabanProvedIsFalse :
      continuumLimitUniformBalabanProved ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    promotions :
      List YMBalabanContinuumLimitPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      YMBalabanContinuumLimitPromotion →
      ⊥

    targetText :
      String

    targetTextIsCanonical :
      targetText ≡ ymBalabanContinuumTargetText

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ ymBalabanContinuumBoundaryText

open YMBalabanContinuumLimitReceipt public

canonicalYMBalabanContinuumLimitReceipt :
  YMBalabanContinuumLimitReceipt
canonicalYMBalabanContinuumLimitReceipt =
  record
    { status =
        ymBalabanContinuumLimitRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; fortyThreeReceipt =
        FortyThree.canonicalYMFortyThreeStepBalabanTargetReceipt
    ; previousFortyThreeStillOpen =
        refl
    ; previousClayStillFalse =
        refl
    ; targets =
        canonicalYMBalabanContinuumTargets
    ; targetsAreCanonical =
        refl
    ; nonClaims =
        canonicalYMBalabanContinuumNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; fortyThreeStepFiniteTargetRetracted =
        true
    ; fortyThreeStepFiniteTargetRetractedIsTrue =
        refl
    ; finiteInductionMisconceived =
        true
    ; finiteInductionMisconceivedIsTrue =
        refl
    ; qAtBetaPhys6 =
        qAtBetaPhysHundredths
    ; qAtBetaPhys6Is453 =
        refl
    ; qAtBetaPhys6Expands =
        true
    ; qAtBetaPhys6ExpandsIsTrue =
        refl
    ; oneLoopKEstimate =
        oneLoopKEstimateTenths
    ; oneLoopKEstimateIs422 =
        refl
    ; betaStrict =
        betaStrictMillionths
    ; betaStrictIs13631603 =
        refl
    ; oneLoopEstimateInformationalOnly =
        true
    ; oneLoopEstimateInformationalOnlyIsTrue =
        refl
    ; continuumLimitUniformBalabanTarget =
        ⊥
    ; continuumLimitUniformBalabanProved =
        false
    ; continuumLimitUniformBalabanProvedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        ymBalabanContinuumLimitPromotionImpossibleHere
    ; targetText =
        ymBalabanContinuumTargetText
    ; targetTextIsCanonical =
        refl
    ; boundary =
        ymBalabanContinuumBoundaryText
    ; boundaryIsCanonical =
        refl
    }

canonicalYMBalabanContinuumKeepsClayFalse :
  clayYangMillsPromoted canonicalYMBalabanContinuumLimitReceipt ≡ false
canonicalYMBalabanContinuumKeepsClayFalse =
  refl
