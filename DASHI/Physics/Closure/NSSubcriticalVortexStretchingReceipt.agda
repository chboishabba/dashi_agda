module DASHI.Physics.Closure.NSSubcriticalVortexStretchingReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSLadyzhenskayaEnstrophyObstructionReceipt
  as Lady

------------------------------------------------------------------------
-- Sprint 8 NS subcritical vortex-stretching target.
--
-- Split:
--   closed theorem            = transport cancellation / commutator reduction
--                               and the standard Ladyzhenskaya bound
--   failed naive transfer     = Leray + Sobolev gives dE/dt <= C_nu E^3
--   promotion lemma remaining = subcritical vortex-stretching absorption

data NSSubcriticalStatus : Set where
  nsSubcriticalVortexStretchingRecorded_noPromotion :
    NSSubcriticalStatus

data NSSubcriticalResult : Set where
  transportCancellationClosed :
    NSSubcriticalResult

  highLowCommutatorClosed :
    NSSubcriticalResult

  kMinusHalfSuppressionRetracted :
    NSSubcriticalResult

  standardLadyzhenskayaCubicObstruction :
    NSSubcriticalResult

  subcriticalAbsorptionIsLiveClayLemma :
    NSSubcriticalResult

canonicalNSSubcriticalResults :
  List NSSubcriticalResult
canonicalNSSubcriticalResults =
  transportCancellationClosed
  ∷ highLowCommutatorClosed
  ∷ kMinusHalfSuppressionRetracted
  ∷ standardLadyzhenskayaCubicObstruction
  ∷ subcriticalAbsorptionIsLiveClayLemma
  ∷ []

data NSSubcriticalNonClaim : Set where
  cubicEnstrophyODEDoesNotCloseLargeData :
    NSSubcriticalNonClaim

  noSerrinControl :
    NSSubcriticalNonClaim

  noPointwiseEnstrophyControl :
    NSSubcriticalNonClaim

  noClayPromotion :
    NSSubcriticalNonClaim

canonicalNSSubcriticalNonClaims :
  List NSSubcriticalNonClaim
canonicalNSSubcriticalNonClaims =
  cubicEnstrophyODEDoesNotCloseLargeData
  ∷ noSerrinControl
  ∷ noPointwiseEnstrophyControl
  ∷ noClayPromotion
  ∷ []

data NSSubcriticalPromotion : Set where

nsSubcriticalPromotionImpossibleHere :
  NSSubcriticalPromotion →
  ⊥
nsSubcriticalPromotionImpossibleHere ()

enstrophyPower : Nat
enstrophyPower =
  3

serrinTimeExponent : Nat
serrinTimeExponent =
  4

serrinSpaceExponent : Nat
serrinSpaceExponent =
  4

nsSubcriticalSummary : String
nsSubcriticalSummary =
  "Sprint 8 NS: the corrected Ladyzhenskaya estimate gives dE/dt <= C_nu E^3 for E=||grad u||_2^2. Clay would require subcritical vortex-stretching absorption with no Serrin, BKM, H118, L-infinity, or continuation input."

nsSubcriticalBoundary : String
nsSubcriticalBoundary =
  "This receipt records the standard cubic enstrophy obstruction and the exact subcritical absorption target. It does not prove Serrin control, pointwise enstrophy control, no finite-time blowup, global smoothness, uniqueness, or Clay Navier-Stokes."

record NSSubcriticalVortexStretchingReceipt : Setω where
  field
    status :
      NSSubcriticalStatus

    statusIsCanonical :
      status ≡ nsSubcriticalVortexStretchingRecorded_noPromotion

    ladyzhenskayaReceipt :
      Lady.NSLadyzhenskayaEnstrophyObstructionReceipt

    previousClayStillFalse :
      Lady.clayNavierStokesPromoted ladyzhenskayaReceipt ≡ false

    previousPointwiseEnstrophyStillOpen :
      Lady.pointwiseEnstrophyControlProved ladyzhenskayaReceipt ≡ false

    results :
      List NSSubcriticalResult

    resultsAreCanonical :
      results ≡ canonicalNSSubcriticalResults

    nonClaims :
      List NSSubcriticalNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalNSSubcriticalNonClaims

    transportCancellation :
      Bool

    transportCancellationIsTrue :
      transportCancellation ≡ true

    highLowEqualsCommutator :
      Bool

    highLowEqualsCommutatorIsTrue :
      highLowEqualsCommutator ≡ true

    kMinusHalfRetracted :
      Bool

    kMinusHalfRetractedIsTrue :
      kMinusHalfRetracted ≡ true

    standardLadyzhenskayaBoundRecorded :
      Bool

    standardLadyzhenskayaBoundRecordedIsTrue :
      standardLadyzhenskayaBoundRecorded ≡ true

    standardEnstrophyODEPower :
      Nat

    standardEnstrophyODEPowerIs3 :
      standardEnstrophyODEPower ≡ enstrophyPower

    requiredSerrinTimeExponent :
      Nat

    requiredSerrinTimeExponentIs4 :
      requiredSerrinTimeExponent ≡ serrinTimeExponent

    requiredSerrinSpaceExponent :
      Nat

    requiredSerrinSpaceExponentIs4 :
      requiredSerrinSpaceExponent ≡ serrinSpaceExponent

    subcriticalVortexStretchingAbsorption :
      Set

    subcriticalVortexStretchingAbsorptionProved :
      Bool

    subcriticalVortexStretchingAbsorptionProvedIsFalse :
      subcriticalVortexStretchingAbsorptionProved ≡ false

    ladyzhenskayaObstructionSharpness :
      Set

    ladyzhenskayaObstructionSharpnessProved :
      Bool

    ladyzhenskayaObstructionSharpnessProvedIsFalse :
      ladyzhenskayaObstructionSharpnessProved ≡ false

    pointwiseEnstrophyControl :
      Set

    pointwiseEnstrophyControlProved :
      Bool

    pointwiseEnstrophyControlProvedIsFalse :
      pointwiseEnstrophyControlProved ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List NSSubcriticalPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSSubcriticalPromotion →
      ⊥

    summary :
      String

    summaryIsCanonical :
      summary ≡ nsSubcriticalSummary

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ nsSubcriticalBoundary

open NSSubcriticalVortexStretchingReceipt public

canonicalNSSubcriticalVortexStretchingReceipt :
  NSSubcriticalVortexStretchingReceipt
canonicalNSSubcriticalVortexStretchingReceipt =
  record
    { status =
        nsSubcriticalVortexStretchingRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; ladyzhenskayaReceipt =
        Lady.canonicalNSLadyzhenskayaEnstrophyObstructionReceipt
    ; previousClayStillFalse =
        refl
    ; previousPointwiseEnstrophyStillOpen =
        refl
    ; results =
        canonicalNSSubcriticalResults
    ; resultsAreCanonical =
        refl
    ; nonClaims =
        canonicalNSSubcriticalNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; transportCancellation =
        true
    ; transportCancellationIsTrue =
        refl
    ; highLowEqualsCommutator =
        true
    ; highLowEqualsCommutatorIsTrue =
        refl
    ; kMinusHalfRetracted =
        true
    ; kMinusHalfRetractedIsTrue =
        refl
    ; standardLadyzhenskayaBoundRecorded =
        true
    ; standardLadyzhenskayaBoundRecordedIsTrue =
        refl
    ; standardEnstrophyODEPower =
        enstrophyPower
    ; standardEnstrophyODEPowerIs3 =
        refl
    ; requiredSerrinTimeExponent =
        serrinTimeExponent
    ; requiredSerrinTimeExponentIs4 =
        refl
    ; requiredSerrinSpaceExponent =
        serrinSpaceExponent
    ; requiredSerrinSpaceExponentIs4 =
        refl
    ; subcriticalVortexStretchingAbsorption =
        ⊥
    ; subcriticalVortexStretchingAbsorptionProved =
        false
    ; subcriticalVortexStretchingAbsorptionProvedIsFalse =
        refl
    ; ladyzhenskayaObstructionSharpness =
        ⊥
    ; ladyzhenskayaObstructionSharpnessProved =
        false
    ; ladyzhenskayaObstructionSharpnessProvedIsFalse =
        refl
    ; pointwiseEnstrophyControl =
        ⊥
    ; pointwiseEnstrophyControlProved =
        false
    ; pointwiseEnstrophyControlProvedIsFalse =
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
        nsSubcriticalPromotionImpossibleHere
    ; summary =
        nsSubcriticalSummary
    ; summaryIsCanonical =
        refl
    ; boundary =
        nsSubcriticalBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalNSSubcriticalKeepsClayFalse :
  clayNavierStokesPromoted
    canonicalNSSubcriticalVortexStretchingReceipt
  ≡
  false
canonicalNSSubcriticalKeepsClayFalse =
  refl
