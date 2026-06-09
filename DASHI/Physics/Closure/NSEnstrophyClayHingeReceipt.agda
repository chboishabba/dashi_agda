module DASHI.Physics.Closure.NSEnstrophyClayHingeReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSCommutatorEquivalenceReceipt as NS

------------------------------------------------------------------------
-- Navier-Stokes enstrophy Clay hinge.
--
-- Sprint 6 correction.  Commutator Lipschitz control is not a shortcut: it
-- is equivalent in proof strength to pointwise enstrophy / no-blowup control.
-- The live analytic hinge is vortex-stretching absorption without hidden
-- Serrin, BKM, global H118, or L-infinity input.

data NSEnstrophyClayHingeStatus : Set where
  nsEnstrophyClayHingeRecorded_noPromotion :
    NSEnstrophyClayHingeStatus

data NSEnstrophyHingeLemma : Set where
  transportTermEnergyCancellation :
    NSEnstrophyHingeLemma

  highLowEqualsCommutator :
    NSEnstrophyHingeLemma

  commutatorEquivalentToEnstrophy :
    NSEnstrophyHingeLemma

  vortexStretchingAbsorption :
    NSEnstrophyHingeLemma

  pointwiseEnstrophyControl :
    NSEnstrophyHingeLemma

  noFiniteTimeBlowup :
    NSEnstrophyHingeLemma

  clayNSFromEnstrophy :
    NSEnstrophyHingeLemma

canonicalNSEnstrophyHingePath : List NSEnstrophyHingeLemma
canonicalNSEnstrophyHingePath =
  transportTermEnergyCancellation
  ∷ highLowEqualsCommutator
  ∷ commutatorEquivalentToEnstrophy
  ∷ vortexStretchingAbsorption
  ∷ pointwiseEnstrophyControl
  ∷ noFiniteTimeBlowup
  ∷ clayNSFromEnstrophy
  ∷ []

data NSEnstrophyNonClaim : Set where
  commutatorEquivalenceIsNotClayProof :
    NSEnstrophyNonClaim

  vortexStretchingAbsorptionNotProved :
    NSEnstrophyNonClaim

  noSerrinBKMH118InputAllowed :
    NSEnstrophyNonClaim

  noClayPromotion :
    NSEnstrophyNonClaim

canonicalNSEnstrophyNonClaims : List NSEnstrophyNonClaim
canonicalNSEnstrophyNonClaims =
  commutatorEquivalenceIsNotClayProof
  ∷ vortexStretchingAbsorptionNotProved
  ∷ noSerrinBKMH118InputAllowed
  ∷ noClayPromotion
  ∷ []

data NSEnstrophyClayHingePromotion : Set where

nsEnstrophyClayHingePromotionImpossibleHere :
  NSEnstrophyClayHingePromotion →
  ⊥
nsEnstrophyClayHingePromotionImpossibleHere ()

nsEnstrophyHingeText : String
nsEnstrophyHingeText =
  "VortexStretchingAbsorption from Leray energy alone is the live NS Clay hinge; CommutatorLipschitzControlWithoutRegularity is equivalent in role to PointwiseEnstrophyControl."

nsEnstrophyBoundaryText : String
nsEnstrophyBoundaryText =
  "This receipt records the enstrophy/blowup hinge and circularity guard only. It does not prove vortex-stretching absorption, pointwise enstrophy, no blowup, global smoothness, uniqueness, or Clay NS."

record NSEnstrophyClayHingeReceipt : Setω where
  field
    status :
      NSEnstrophyClayHingeStatus

    statusIsCanonical :
      status ≡ nsEnstrophyClayHingeRecorded_noPromotion

    commutatorReceipt :
      NS.NSCommutatorEquivalenceReceipt

    commutatorEquivalentToBlowupRecorded :
      NS.commutatorLipschitzEquivalentToBlowupPreventionRecorded
        commutatorReceipt
      ≡
      true

    previousClayStillFalse :
      NS.clayNavierStokesPromoted commutatorReceipt ≡ false

    path :
      List NSEnstrophyHingeLemma

    pathIsCanonical :
      path ≡ canonicalNSEnstrophyHingePath

    nonClaims :
      List NSEnstrophyNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalNSEnstrophyNonClaims

    transportTermCancellation :
      Bool

    transportTermCancellationIsTrue :
      transportTermCancellation ≡ true

    highLowEqualsCommutatorRecorded :
      Bool

    highLowEqualsCommutatorRecordedIsTrue :
      highLowEqualsCommutatorRecorded ≡ true

    commutatorEquivalentToEnstrophyRecorded :
      Bool

    commutatorEquivalentToEnstrophyRecordedIsTrue :
      commutatorEquivalentToEnstrophyRecorded ≡ true

    liveClayHinge :
      Set

    pointwiseEnstrophyControlTarget :
      Set

    noSerrinInput :
      Bool

    noSerrinInputIsTrue :
      noSerrinInput ≡ true

    noBKMInput :
      Bool

    noBKMInputIsTrue :
      noBKMInput ≡ true

    noGlobalH118Input :
      Bool

    noGlobalH118InputIsTrue :
      noGlobalH118Input ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List NSEnstrophyClayHingePromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSEnstrophyClayHingePromotion →
      ⊥

    hingeText :
      String

    hingeTextIsCanonical :
      hingeText ≡ nsEnstrophyHingeText

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ nsEnstrophyBoundaryText

open NSEnstrophyClayHingeReceipt public

canonicalNSEnstrophyClayHingeReceipt :
  NSEnstrophyClayHingeReceipt
canonicalNSEnstrophyClayHingeReceipt =
  record
    { status =
        nsEnstrophyClayHingeRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; commutatorReceipt =
        NS.canonicalNSCommutatorEquivalenceReceipt
    ; commutatorEquivalentToBlowupRecorded =
        refl
    ; previousClayStillFalse =
        refl
    ; path =
        canonicalNSEnstrophyHingePath
    ; pathIsCanonical =
        refl
    ; nonClaims =
        canonicalNSEnstrophyNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; transportTermCancellation =
        true
    ; transportTermCancellationIsTrue =
        refl
    ; highLowEqualsCommutatorRecorded =
        true
    ; highLowEqualsCommutatorRecordedIsTrue =
        refl
    ; commutatorEquivalentToEnstrophyRecorded =
        true
    ; commutatorEquivalentToEnstrophyRecordedIsTrue =
        refl
    ; liveClayHinge =
        ⊥
    ; pointwiseEnstrophyControlTarget =
        ⊥
    ; noSerrinInput =
        true
    ; noSerrinInputIsTrue =
        refl
    ; noBKMInput =
        true
    ; noBKMInputIsTrue =
        refl
    ; noGlobalH118Input =
        true
    ; noGlobalH118InputIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        nsEnstrophyClayHingePromotionImpossibleHere
    ; hingeText =
        nsEnstrophyHingeText
    ; hingeTextIsCanonical =
        refl
    ; boundary =
        nsEnstrophyBoundaryText
    ; boundaryIsCanonical =
        refl
    }

canonicalNSEnstrophyKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSEnstrophyClayHingeReceipt ≡ false
canonicalNSEnstrophyKeepsClayFalse =
  refl
