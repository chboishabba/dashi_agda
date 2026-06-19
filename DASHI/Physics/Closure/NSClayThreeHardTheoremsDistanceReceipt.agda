module DASHI.Physics.Closure.NSClayThreeHardTheoremsDistanceReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Candidate-only Clay-distance receipt for the two hard analytic walls.
-- The historical three-hard-theorem ledger has been superseded/refined:
-- BoundaryHB_Correct is now discharged by pointwise kornBiaxialBound /
-- nondegeneracy, so the canonical hard walls are just:
--   A = KornLevelSet
--   C = collapseImpossible
--
-- The first six packages are marked as formalization/standard packages.
-- The conditional theorem is recorded before Clay, and Clay promotion is
-- kept false.

data NSClayThreeHardTheoremsDistanceStatus : Set where
  candidateOnlyExactDistanceRecorded :
    NSClayThreeHardTheoremsDistanceStatus

data NSClayThreeHardTheoremsDistanceStep : Set where
  A_KornLevelSet :
    NSClayThreeHardTheoremsDistanceStep

  B_BoundaryHB :
    NSClayThreeHardTheoremsDistanceStep

  C_collapseImpossible :
    NSClayThreeHardTheoremsDistanceStep

canonicalNSClayThreeHardTheoremsDistanceSteps :
  List NSClayThreeHardTheoremsDistanceStep
canonicalNSClayThreeHardTheoremsDistanceSteps =
  A_KornLevelSet
  ∷ C_collapseImpossible
  ∷ []

data NSClayThreeHardTheoremsPackageTrack : Set where
  formalizationPackage1 :
    NSClayThreeHardTheoremsPackageTrack

  standardPackage1 :
    NSClayThreeHardTheoremsPackageTrack

  formalizationPackage2 :
    NSClayThreeHardTheoremsPackageTrack

  standardPackage2 :
    NSClayThreeHardTheoremsPackageTrack

  formalizationPackage3 :
    NSClayThreeHardTheoremsPackageTrack

  standardPackage3 :
    NSClayThreeHardTheoremsPackageTrack

canonicalNSClayThreeHardTheoremsPackageTrack :
  List NSClayThreeHardTheoremsPackageTrack
canonicalNSClayThreeHardTheoremsPackageTrack =
  formalizationPackage1
  ∷ standardPackage1
  ∷ formalizationPackage2
  ∷ standardPackage2
  ∷ formalizationPackage3
  ∷ standardPackage3
  ∷ []

data NSClayThreeHardTheoremsDistancePromotion : Set where

nsClayThreeHardTheoremsDistancePromotionImpossibleHere :
  NSClayThreeHardTheoremsDistancePromotion →
  ⊥
nsClayThreeHardTheoremsDistancePromotionImpossibleHere ()

nsClayThreeHardTheoremsDistanceStatement : String
nsClayThreeHardTheoremsDistanceStatement =
  "Candidate-only Clay distance: A = KornLevelSet and C = collapseImpossible; BoundaryHB_Correct is now closed by pointwise kornBiaxialBound/nondegeneracy and is not a hard wall; the historical three-hard-theorem ledger is superseded/refined; the first six packages are formalization/standard packages; the conditional theorem is recorded before Clay; Clay promotion is false."

record NSClayThreeHardTheoremsDistanceReceipt : Setω where
  field
    status :
      NSClayThreeHardTheoremsDistanceStatus

    statusIsCanonical :
      status ≡ candidateOnlyExactDistanceRecorded

    exactDistanceSteps :
      List NSClayThreeHardTheoremsDistanceStep

    exactDistanceStepsAreCanonical :
      exactDistanceSteps ≡ canonicalNSClayThreeHardTheoremsDistanceSteps

    exactDistanceStepCount :
      Nat

    exactDistanceStepCountIs2 :
      exactDistanceStepCount ≡ 2

    packageTrack :
      List NSClayThreeHardTheoremsPackageTrack

    packageTrackAreCanonical :
      packageTrack ≡ canonicalNSClayThreeHardTheoremsPackageTrack

    packageTrackCount :
      Nat

    packageTrackCountIs6 :
      packageTrackCount ≡ 6

    conditionalTheoremBeforeClay :
      Bool

    conditionalTheoremBeforeClayIsTrue :
      conditionalTheoremBeforeClay ≡ true

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsClayThreeHardTheoremsDistanceStatement

    promotionFlags :
      List NSClayThreeHardTheoremsDistancePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSClayThreeHardTheoremsDistanceReceipt public

canonicalNSClayThreeHardTheoremsDistanceReceipt :
  NSClayThreeHardTheoremsDistanceReceipt
canonicalNSClayThreeHardTheoremsDistanceReceipt =
  record
    { status =
        candidateOnlyExactDistanceRecorded
    ; statusIsCanonical =
        refl
    ; exactDistanceSteps =
        canonicalNSClayThreeHardTheoremsDistanceSteps
    ; exactDistanceStepsAreCanonical =
        refl
    ; exactDistanceStepCount =
        2
    ; exactDistanceStepCountIs2 =
        refl
    ; packageTrack =
        canonicalNSClayThreeHardTheoremsPackageTrack
    ; packageTrackAreCanonical =
        refl
    ; packageTrackCount =
        6
    ; packageTrackCountIs6 =
        refl
    ; conditionalTheoremBeforeClay =
        true
    ; conditionalTheoremBeforeClayIsTrue =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; statement =
        nsClayThreeHardTheoremsDistanceStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "A records KornLevelSet as a canonical hard-theorem distance anchor"
        ∷ "B is retained as historical ledger context for BoundaryHB_Correct, now discharged by pointwise kornBiaxialBound/nondegeneracy"
        ∷ "C records collapseImpossible as a canonical hard-theorem distance anchor"
        ∷ "The historical three-hard-theorem ledger is superseded/refined to two canonical hard walls"
        ∷ "The first six packages are formalization/standard packages"
        ∷ "The conditional theorem sits before any Clay promotion"
        ∷ "Clay promotion remains false"
        ∷ []
    }
