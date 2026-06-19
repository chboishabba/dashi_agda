module DASHI.Physics.Closure.NSCalc12RouteCalibrationReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- NS Calc12 post-real route calibration receipt.
--
-- Candidate-only route calibration surface for the post-real Calc12 lane.
-- It records the fitted beta, its CI above 1, the regularity-consistent
-- decision, the empirical delta, a low-rSquared caveat, and the local
-- fail-closed boundary.  No theorem authority, no calculation authority,
-- and no Clay promotion are claimed here.

data NSCalc12RouteCalibrationMode : Set where
  candidateOnlyRouteCalibration :
    NSCalc12RouteCalibrationMode

data NSCalc12RouteCalibrationPromotion : Set where

nsCalc12RouteCalibrationPromotionImpossibleHere :
  NSCalc12RouteCalibrationPromotion →
  ⊥
nsCalc12RouteCalibrationPromotionImpossibleHere ()

nsCalc12RouteCalibrationSummary : String
nsCalc12RouteCalibrationSummary =
  "Calc12 post-real route calibration receipt: beta is 2.2754974180523737, the CI stays above 1, the decision is regularity_consistent, deltaEmpirical is approximately 1.275, rSquared is low and only a caveat, target delta = 1 is sufficient, and theorem authority, calculation authority, and Clay promotion remain false."

data NSCalc12RouteCalibrationBoundary : Set where
  candidateOnlyCalibrationRecorded :
    NSCalc12RouteCalibrationBoundary

canonicalNSCalc12RouteCalibrationBoundary :
  List NSCalc12RouteCalibrationBoundary
canonicalNSCalc12RouteCalibrationBoundary =
  candidateOnlyCalibrationRecorded
  ∷ []

record NSCalc12RouteCalibrationReceipt : Set where
  field
    mode :
      NSCalc12RouteCalibrationMode

    modeIsCandidateOnlyRouteCalibration :
      mode ≡ candidateOnlyRouteCalibration

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    beta :
      String

    betaIsCanonical :
      beta ≡ "2.2754974180523737"

    ciLower :
      String

    ciLowerIsCanonical :
      ciLower ≡ "2.129779448947756"

    ciUpper :
      String

    ciUpperIsCanonical :
      ciUpper ≡ "2.4212153871569915"

    decision :
      String

    decisionIsCanonical :
      decision ≡ "regularity_consistent"

    deltaEmpirical :
      String

    deltaEmpiricalIsCanonical :
      deltaEmpirical ≡ "1.2754974180523737"

    rSquaredCaveat :
      String

    rSquaredCaveatIsCanonical :
      rSquaredCaveat
      ≡ "low rSquared caveat: this candidate route is recorded, but fit quality remains limited and should not be read as a theorem."

    targetDeltaSufficient :
      String

    targetDeltaSufficientIsCanonical :
      targetDeltaSufficient ≡ "target delta = 1 is sufficient"

    theoremAuthority :
      Bool

    theoremAuthorityIsFalse :
      theoremAuthority ≡ false

    calculationAuthority :
      Bool

    calculationAuthorityIsFalse :
      calculationAuthority ≡ false

    clayPromotion :
      Bool

    clayPromotionIsFalse :
      clayPromotion ≡ false

    summary :
      String

    summaryIsCanonical :
      summary ≡ nsCalc12RouteCalibrationSummary

    promotionFlags :
      List NSCalc12RouteCalibrationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSCalc12RouteCalibrationReceipt public

canonicalNSCalc12RouteCalibrationReceipt :
  NSCalc12RouteCalibrationReceipt
canonicalNSCalc12RouteCalibrationReceipt =
  record
    { mode =
        candidateOnlyRouteCalibration
    ; modeIsCandidateOnlyRouteCalibration =
        refl
    ; candidateOnly =
        true
    ; candidateOnlyIsTrue =
        refl
    ; beta =
        "2.2754974180523737"
    ; betaIsCanonical =
        refl
    ; ciLower =
        "2.129779448947756"
    ; ciLowerIsCanonical =
        refl
    ; ciUpper =
        "2.4212153871569915"
    ; ciUpperIsCanonical =
        refl
    ; decision =
        "regularity_consistent"
    ; decisionIsCanonical =
        refl
    ; deltaEmpirical =
        "1.2754974180523737"
    ; deltaEmpiricalIsCanonical =
        refl
    ; rSquaredCaveat =
        "low rSquared caveat: this candidate route is recorded, but fit quality remains limited and should not be read as a theorem."
    ; rSquaredCaveatIsCanonical =
        refl
    ; targetDeltaSufficient =
        "target delta = 1 is sufficient"
    ; targetDeltaSufficientIsCanonical =
        refl
    ; theoremAuthority =
        false
    ; theoremAuthorityIsFalse =
        refl
    ; calculationAuthority =
        false
    ; calculationAuthorityIsFalse =
        refl
    ; clayPromotion =
        false
    ; clayPromotionIsFalse =
        refl
    ; summary =
        nsCalc12RouteCalibrationSummary
    ; summaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Calc12 route calibration is candidate-only"
        ∷ "Beta is recorded at 2.2754974180523737 with the CI above 1"
        ∷ "Decision is regularity_consistent and deltaEmpirical is approximately 1.275"
        ∷ "Low rSquared is kept as a caveat, not as theorem authority"
        ∷ "Target delta = 1 is sufficient"
        ∷ "Theorem authority, calculation authority, and Clay promotion remain false"
        ∷ []
    }

canonicalNSCalc12RouteCalibrationMode :
  NSCalc12RouteCalibrationMode
canonicalNSCalc12RouteCalibrationMode =
  candidateOnlyRouteCalibration

canonicalNSCalc12RouteCalibrationModeIsCandidateOnly :
  mode canonicalNSCalc12RouteCalibrationReceipt
  ≡ canonicalNSCalc12RouteCalibrationMode
canonicalNSCalc12RouteCalibrationModeIsCandidateOnly =
  refl

canonicalNSCalc12RouteCalibrationTheoremAuthorityFalse :
  theoremAuthority canonicalNSCalc12RouteCalibrationReceipt ≡ false
canonicalNSCalc12RouteCalibrationTheoremAuthorityFalse =
  refl

canonicalNSCalc12RouteCalibrationCalculationAuthorityFalse :
  calculationAuthority canonicalNSCalc12RouteCalibrationReceipt ≡ false
canonicalNSCalc12RouteCalibrationCalculationAuthorityFalse =
  refl

canonicalNSCalc12RouteCalibrationClayPromotionFalse :
  clayPromotion canonicalNSCalc12RouteCalibrationReceipt ≡ false
canonicalNSCalc12RouteCalibrationClayPromotionFalse =
  refl
