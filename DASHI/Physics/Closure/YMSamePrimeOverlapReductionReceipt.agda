module DASHI.Physics.Closure.YMSamePrimeOverlapReductionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.KPUniformVolumeBoundReceipt as KP

------------------------------------------------------------------------
-- YM same-prime overlap reduction.
--
-- This is the YM1 receipt in the Paper 3 roadmap.  It records the
-- carrier-side support reduction only: cross-prime disconnected plaquettes
-- are excluded from the retained KP overlap set, and the retained local
-- polymer problem is same-prime/single-prime.  It does not assert activity
-- factorisation, a numeric KP bound, a Balaban induction, or a continuum
-- Yang-Mills theorem.

data YMSamePrimeOverlapReductionStatus : Set where
  samePrimeOverlapReductionRecorded :
    YMSamePrimeOverlapReductionStatus

data YMPlaquettePrimeSupportRelation : Set where
  disjointPrimeSupportMeansDisconnectedPlaquetteSupport :
    YMPlaquettePrimeSupportRelation

data YMKPOverlapSetVerdict : Set where
  retainedKPOverlapSetIsSamePrimeOnly :
    YMKPOverlapSetVerdict

data YMActivityFactorisationBoundary : Set where
  activityFactorisationNotUsedInReduction :
    YMActivityFactorisationBoundary

data YMSamePrimeReductionOpenObligation : Set where
  proveActualCarrierSupportDisjointness :
    YMSamePrimeReductionOpenObligation

  defineActualWilsonActivityBeforeKPUse :
    YMSamePrimeReductionOpenObligation

  proveSamePrimeLocalSumBound :
    YMSamePrimeReductionOpenObligation

canonicalYMSamePrimeReductionOpenObligations :
  List YMSamePrimeReductionOpenObligation
canonicalYMSamePrimeReductionOpenObligations =
  proveActualCarrierSupportDisjointness
  ∷ defineActualWilsonActivityBeforeKPUse
  ∷ proveSamePrimeLocalSumBound
  ∷ []

data YMSamePrimeReductionNonClaim : Set where
  noActivityMultiplicativityClaim :
    YMSamePrimeReductionNonClaim

  noKPSumBoundClaim :
    YMSamePrimeReductionNonClaim

  noBalabanRGClaim :
    YMSamePrimeReductionNonClaim

  noContinuumYangMillsClaim :
    YMSamePrimeReductionNonClaim

  noClayYangMillsPromotion :
    YMSamePrimeReductionNonClaim

canonicalYMSamePrimeReductionNonClaims :
  List YMSamePrimeReductionNonClaim
canonicalYMSamePrimeReductionNonClaims =
  noActivityMultiplicativityClaim
  ∷ noKPSumBoundClaim
  ∷ noBalabanRGClaim
  ∷ noContinuumYangMillsClaim
  ∷ noClayYangMillsPromotion
  ∷ []

data YMSamePrimeReductionPromotion : Set where

ymSamePrimeReductionPromotionImpossibleHere :
  YMSamePrimeReductionPromotion →
  ⊥
ymSamePrimeReductionPromotionImpossibleHere ()

retainedPrimeFactorCount :
  Nat
retainedPrimeFactorCount =
  1

originalSSPPrimeCount :
  Nat
originalSSPPrimeCount =
  15

samePrimeReductionSummary :
  String
samePrimeReductionSummary =
  "YM1: the KP overlap set is reduced from cross-prime disconnected support to retained same-prime polymers; activity factorisation and local-sum bounds remain separate obligations."

record YMSamePrimeOverlapReductionReceipt : Setω where
  field
    status :
      YMSamePrimeOverlapReductionStatus

    statusIsCanonical :
      status ≡ samePrimeOverlapReductionRecorded

    consumedKPUniformVolumeReceipt :
      KP.KPUniformVolumeBoundReceipt

    kpReceiptRetainsSamePrime :
      KP.kpOverlapReductionStatus consumedKPUniformVolumeReceipt
      ≡
      KP.kpOverlapReducesToSamePrime

    kpReceiptRejectsNaiveActivityFactorisation :
      KP.naiveActivityFactorisationVerdict consumedKPUniformVolumeReceipt
      ≡
      KP.naiveActivityFactorisationRejected

    supportRelation :
      YMPlaquettePrimeSupportRelation

    supportRelationIsDisjoint :
      supportRelation
      ≡
      disjointPrimeSupportMeansDisconnectedPlaquetteSupport

    retainedOverlapVerdict :
      YMKPOverlapSetVerdict

    retainedOverlapVerdictIsSamePrime :
      retainedOverlapVerdict ≡ retainedKPOverlapSetIsSamePrimeOnly

    factorisationBoundary :
      YMActivityFactorisationBoundary

    factorisationBoundaryIsNotUsed :
      factorisationBoundary ≡ activityFactorisationNotUsedInReduction

    originalPrimeFactors :
      Nat

    originalPrimeFactorsIsSSP :
      originalPrimeFactors ≡ originalSSPPrimeCount

    retainedPrimeFactors :
      Nat

    retainedPrimeFactorsIsSinglePrime :
      retainedPrimeFactors ≡ retainedPrimeFactorCount

    openObligations :
      List YMSamePrimeReductionOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalYMSamePrimeReductionOpenObligations

    nonClaims :
      List YMSamePrimeReductionNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalYMSamePrimeReductionNonClaims

    continuumYangMillsPromoted :
      Bool

    continuumYangMillsPromotedIsFalse :
      continuumYangMillsPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    summary :
      String

    summaryIsCanonical :
      summary ≡ samePrimeReductionSummary

open YMSamePrimeOverlapReductionReceipt public

canonicalYMSamePrimeOverlapReductionReceipt :
  YMSamePrimeOverlapReductionReceipt
canonicalYMSamePrimeOverlapReductionReceipt =
  record
    { status =
        samePrimeOverlapReductionRecorded
    ; statusIsCanonical =
        refl
    ; consumedKPUniformVolumeReceipt =
        KP.canonicalKPUniformVolumeBoundReceipt
    ; kpReceiptRetainsSamePrime =
        refl
    ; kpReceiptRejectsNaiveActivityFactorisation =
        refl
    ; supportRelation =
        disjointPrimeSupportMeansDisconnectedPlaquetteSupport
    ; supportRelationIsDisjoint =
        refl
    ; retainedOverlapVerdict =
        retainedKPOverlapSetIsSamePrimeOnly
    ; retainedOverlapVerdictIsSamePrime =
        refl
    ; factorisationBoundary =
        activityFactorisationNotUsedInReduction
    ; factorisationBoundaryIsNotUsed =
        refl
    ; originalPrimeFactors =
        originalSSPPrimeCount
    ; originalPrimeFactorsIsSSP =
        refl
    ; retainedPrimeFactors =
        retainedPrimeFactorCount
    ; retainedPrimeFactorsIsSinglePrime =
        refl
    ; openObligations =
        canonicalYMSamePrimeReductionOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; nonClaims =
        canonicalYMSamePrimeReductionNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; continuumYangMillsPromoted =
        false
    ; continuumYangMillsPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; summary =
        samePrimeReductionSummary
    ; summaryIsCanonical =
        refl
    }

ymSamePrimeReductionNoClay :
  clayYangMillsPromoted canonicalYMSamePrimeOverlapReductionReceipt
  ≡
  false
ymSamePrimeReductionNoClay =
  refl
