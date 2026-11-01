module DASHI.Physics.Closure.NSLadyzhenskayaCubicObstructionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSLadyzhenskayaEnstrophyObstructionReceipt
  as Sprint7

------------------------------------------------------------------------
-- NS Ladyzhenskaya cubic obstruction.
--
-- Sprint 8 corrects the live obstruction statement.  The standard 3D
-- Ladyzhenskaya/Gagliardo-Nirenberg route yields an enstrophy ODE with an
-- E^3 right-hand side for E = ||grad u||_2^2, not a subcritical linear
-- absorption estimate.  Reducing that E^3 to E is the Clay hinge.

data NSLadyzhenskayaCubicStatus : Set where
  nsLadyzhenskayaCubicObstructionRecorded_noPromotion :
    NSLadyzhenskayaCubicStatus

data NSLadyzhenskayaCubicFact : Set where
  predecessorCubicStatementConfirmed :
    NSLadyzhenskayaCubicFact

  interpolationGivesGradL3Cubed :
    NSLadyzhenskayaCubicFact

  youngInequalityGivesCubicEnstrophyODE :
    NSLadyzhenskayaCubicFact

  blowupTimeScalesAsInverseInitialEnstrophySquared :
    NSLadyzhenskayaCubicFact

  subcriticalAbsorptionRequiresThreePowerReduction :
    NSLadyzhenskayaCubicFact

  standardSobolevLerayToolsDoNotClose :
    NSLadyzhenskayaCubicFact

canonicalNSLadyzhenskayaCubicFacts :
  List NSLadyzhenskayaCubicFact
canonicalNSLadyzhenskayaCubicFacts =
  predecessorCubicStatementConfirmed
  ∷ interpolationGivesGradL3Cubed
  ∷ youngInequalityGivesCubicEnstrophyODE
  ∷ blowupTimeScalesAsInverseInitialEnstrophySquared
  ∷ subcriticalAbsorptionRequiresThreePowerReduction
  ∷ standardSobolevLerayToolsDoNotClose
  ∷ []

data NSLadyzhenskayaCubicNonClaim : Set where
  cubicObstructionIsNotBlowupProof :
    NSLadyzhenskayaCubicNonClaim

  noSubcriticalVortexStretchingAbsorption :
    NSLadyzhenskayaCubicNonClaim

  noPointwiseEnstrophyControl :
    NSLadyzhenskayaCubicNonClaim

  noClayPromotion :
    NSLadyzhenskayaCubicNonClaim

canonicalNSLadyzhenskayaCubicNonClaims :
  List NSLadyzhenskayaCubicNonClaim
canonicalNSLadyzhenskayaCubicNonClaims =
  cubicObstructionIsNotBlowupProof
  ∷ noSubcriticalVortexStretchingAbsorption
  ∷ noPointwiseEnstrophyControl
  ∷ noClayPromotion
  ∷ []

data NSLadyzhenskayaCubicPromotion : Set where

nsLadyzhenskayaCubicPromotionImpossibleHere :
  NSLadyzhenskayaCubicPromotion →
  ⊥
nsLadyzhenskayaCubicPromotionImpossibleHere ()

enstrophyODEPower : Nat
enstrophyODEPower =
  3

powersToReduceForSubcriticalAbsorption : Nat
powersToReduceForSubcriticalAbsorption =
  3

classicalReferenceStartYear : Nat
classicalReferenceStartYear =
  1959

classicalReferenceEndYear : Nat
classicalReferenceEndYear =
  1963

nsLadyzhenskayaCubicSummary : String
nsLadyzhenskayaCubicSummary =
  "Sprint 8 NS: the corrected Ladyzhenskaya/Prodi/Serrin obstruction is cubic in enstrophy. Standard Sobolev/Leray tools give dE/dt <= C_nu E^3; Clay needs subcritical vortex-stretching absorption reducing E^3 to E."

nsLadyzhenskayaCubicBoundary : String
nsLadyzhenskayaCubicBoundary =
  "This receipt records the sharp classical cubic obstruction. It does not prove SubcriticalVortexStretchingAbsorption, pointwise enstrophy control, no finite-time blowup, global smoothness, uniqueness, or Clay Navier-Stokes."

record NSLadyzhenskayaCubicObstructionReceipt : Setω where
  field
    status :
      NSLadyzhenskayaCubicStatus

    statusIsCanonical :
      status ≡ nsLadyzhenskayaCubicObstructionRecorded_noPromotion

    sprintSevenReceipt :
      Sprint7.NSLadyzhenskayaEnstrophyObstructionReceipt

    sprintSevenClayStillFalse :
      Sprint7.clayNavierStokesPromoted sprintSevenReceipt ≡ false

    predecessorCubicPowerConfirmed :
      Sprint7.enstrophyODEPower sprintSevenReceipt ≡ 3

    facts :
      List NSLadyzhenskayaCubicFact

    factsAreCanonical :
      facts ≡ canonicalNSLadyzhenskayaCubicFacts

    nonClaims :
      List NSLadyzhenskayaCubicNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalNSLadyzhenskayaCubicNonClaims

    ladyzhenskayaInterpolation3D :
      Set

    vortexStretchingCubicBound :
      Set

    youngGivesCubicEnstrophyODE :
      Bool

    youngGivesCubicEnstrophyODEIsTrue :
      youngGivesCubicEnstrophyODE ≡ true

    enstrophyODEPowerRecorded :
      Nat

    enstrophyODEPowerRecordedIs3 :
      enstrophyODEPowerRecorded ≡ enstrophyODEPower

    subcriticalVortexStretchingAbsorption :
      Set

    subcriticalVortexStretchingAbsorptionProved :
      Bool

    subcriticalVortexStretchingAbsorptionProvedIsFalse :
      subcriticalVortexStretchingAbsorptionProved ≡ false

    enstrophyPowerReductionRequired :
      Nat

    enstrophyPowerReductionRequiredIs3 :
      enstrophyPowerReductionRequired
      ≡
      powersToReduceForSubcriticalAbsorption

    ladyzhenskayaObstructionSharpForLeraySobolev :
      Set

    ladyzhenskayaObstructionSharpForLeraySobolevProved :
      Bool

    ladyzhenskayaObstructionSharpForLeraySobolevProvedIsFalse :
      ladyzhenskayaObstructionSharpForLeraySobolevProved ≡ false

    classicalObstructionStartYear :
      Nat

    classicalObstructionStartYearIs1959 :
      classicalObstructionStartYear ≡ classicalReferenceStartYear

    classicalObstructionEndYear :
      Nat

    classicalObstructionEndYearIs1963 :
      classicalObstructionEndYear ≡ classicalReferenceEndYear

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
      List NSLadyzhenskayaCubicPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSLadyzhenskayaCubicPromotion →
      ⊥

    summary :
      String

    summaryIsCanonical :
      summary ≡ nsLadyzhenskayaCubicSummary

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ nsLadyzhenskayaCubicBoundary

open NSLadyzhenskayaCubicObstructionReceipt public

canonicalNSLadyzhenskayaCubicObstructionReceipt :
  NSLadyzhenskayaCubicObstructionReceipt
canonicalNSLadyzhenskayaCubicObstructionReceipt =
  record
    { status =
        nsLadyzhenskayaCubicObstructionRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; sprintSevenReceipt =
        Sprint7.canonicalNSLadyzhenskayaEnstrophyObstructionReceipt
    ; sprintSevenClayStillFalse =
        refl
    ; predecessorCubicPowerConfirmed =
        refl
    ; facts =
        canonicalNSLadyzhenskayaCubicFacts
    ; factsAreCanonical =
        refl
    ; nonClaims =
        canonicalNSLadyzhenskayaCubicNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; ladyzhenskayaInterpolation3D =
        ⊥
    ; vortexStretchingCubicBound =
        ⊥
    ; youngGivesCubicEnstrophyODE =
        true
    ; youngGivesCubicEnstrophyODEIsTrue =
        refl
    ; enstrophyODEPowerRecorded =
        enstrophyODEPower
    ; enstrophyODEPowerRecordedIs3 =
        refl
    ; subcriticalVortexStretchingAbsorption =
        ⊥
    ; subcriticalVortexStretchingAbsorptionProved =
        false
    ; subcriticalVortexStretchingAbsorptionProvedIsFalse =
        refl
    ; enstrophyPowerReductionRequired =
        powersToReduceForSubcriticalAbsorption
    ; enstrophyPowerReductionRequiredIs3 =
        refl
    ; ladyzhenskayaObstructionSharpForLeraySobolev =
        ⊥
    ; ladyzhenskayaObstructionSharpForLeraySobolevProved =
        false
    ; ladyzhenskayaObstructionSharpForLeraySobolevProvedIsFalse =
        refl
    ; classicalObstructionStartYear =
        classicalReferenceStartYear
    ; classicalObstructionStartYearIs1959 =
        refl
    ; classicalObstructionEndYear =
        classicalReferenceEndYear
    ; classicalObstructionEndYearIs1963 =
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
        nsLadyzhenskayaCubicPromotionImpossibleHere
    ; summary =
        nsLadyzhenskayaCubicSummary
    ; summaryIsCanonical =
        refl
    ; boundary =
        nsLadyzhenskayaCubicBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalNSLadyzhenskayaCubicKeepsClayFalse :
  clayNavierStokesPromoted
    canonicalNSLadyzhenskayaCubicObstructionReceipt
  ≡
  false
canonicalNSLadyzhenskayaCubicKeepsClayFalse =
  refl
