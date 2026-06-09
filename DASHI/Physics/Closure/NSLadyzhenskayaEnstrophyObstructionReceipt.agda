module DASHI.Physics.Closure.NSLadyzhenskayaEnstrophyObstructionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSEnstrophyClayHingeReceipt as Hinge

------------------------------------------------------------------------
-- Ladyzhenskaya enstrophy obstruction.
--
-- Sprint 7 NS result, corrected by the Sprint 8 audit.  The direct
-- vortex-stretching absorption attack recovers the classical
-- Ladyzhenskaya/Prodi/Serrin obstruction: for enstrophy
-- E = ||grad u||_2^2, the standard estimate gives dE/dt <= C_nu E^3.
-- That is a real frontier confirmation, not a Clay proof.

data NSLadyzhenskayaStatus : Set where
  nsLadyzhenskayaObstructionRecorded_noPromotion :
    NSLadyzhenskayaStatus

data NSLadyzhenskayaFact : Set where
  correctedGagliardoNirenberg3D :
    NSLadyzhenskayaFact

  vortexStretchingBoundCubic :
    NSLadyzhenskayaFact

  youngInequalityGivesCubicEnstrophyODE :
    NSLadyzhenskayaFact

  cubicODEEstimateCanBlowUp :
    NSLadyzhenskayaFact

  estimateFailureIsNotSolutionBlowup :
    NSLadyzhenskayaFact

  serrinL4L4InputIsMissing :
    NSLadyzhenskayaFact

  classicalObstructionRediscovered :
    NSLadyzhenskayaFact

canonicalNSLadyzhenskayaFacts : List NSLadyzhenskayaFact
canonicalNSLadyzhenskayaFacts =
  correctedGagliardoNirenberg3D
  ∷ vortexStretchingBoundCubic
  ∷ youngInequalityGivesCubicEnstrophyODE
  ∷ cubicODEEstimateCanBlowUp
  ∷ estimateFailureIsNotSolutionBlowup
  ∷ serrinL4L4InputIsMissing
  ∷ classicalObstructionRediscovered
  ∷ []

data NSLadyzhenskayaNonClaim : Set where
  noVortexStretchingAbsorption :
    NSLadyzhenskayaNonClaim

  noPointwiseEnstrophyControl :
    NSLadyzhenskayaNonClaim

  noNoBlowupTheorem :
    NSLadyzhenskayaNonClaim

  noClayPromotion :
    NSLadyzhenskayaNonClaim

canonicalNSLadyzhenskayaNonClaims : List NSLadyzhenskayaNonClaim
canonicalNSLadyzhenskayaNonClaims =
  noVortexStretchingAbsorption
  ∷ noPointwiseEnstrophyControl
  ∷ noNoBlowupTheorem
  ∷ noClayPromotion
  ∷ []

data NSLadyzhenskayaPromotion : Set where

nsLadyzhenskayaPromotionImpossibleHere :
  NSLadyzhenskayaPromotion →
  ⊥
nsLadyzhenskayaPromotionImpossibleHere ()

enstrophyODEDegree : Nat
enstrophyODEDegree =
  3

requiredSerrinTimeExponent : Nat
requiredSerrinTimeExponent =
  4

requiredSerrinSpaceExponent : Nat
requiredSerrinSpaceExponent =
  4

classicalReferenceStartYear : Nat
classicalReferenceStartYear =
  1959

classicalReferenceEndYear : Nat
classicalReferenceEndYear =
  1963

nsLadyzhenskayaSummary : String
nsLadyzhenskayaSummary =
  "Sprint 7/8 NS: the vortex-stretching absorption attack recovers Ladyzhenskaya/Prodi/Serrin. For E=||grad u||_2^2, Gagliardo-Nirenberg plus Young yields dE/dt <= C_nu E^3; the missing non-circular input is subcritical absorption / L4_t L4_x Serrin control."

nsLadyzhenskayaBoundary : String
nsLadyzhenskayaBoundary =
  "This receipt records an obstruction theorem surface only. It does not prove Serrin control, pointwise enstrophy control, no finite-time blowup, global smoothness, uniqueness, or Clay Navier-Stokes."

record NSLadyzhenskayaEnstrophyObstructionReceipt : Setω where
  field
    status :
      NSLadyzhenskayaStatus

    statusIsCanonical :
      status ≡ nsLadyzhenskayaObstructionRecorded_noPromotion

    hingeReceipt :
      Hinge.NSEnstrophyClayHingeReceipt

    previousClayStillFalse :
      Hinge.clayNavierStokesPromoted hingeReceipt ≡ false

    previousLiveHingeWasOpen :
      Hinge.liveClayHinge hingeReceipt ≡ ⊥

    facts :
      List NSLadyzhenskayaFact

    factsAreCanonical :
      facts ≡ canonicalNSLadyzhenskayaFacts

    nonClaims :
      List NSLadyzhenskayaNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalNSLadyzhenskayaNonClaims

    correctedGagliardoNirenbergRecorded :
      Bool

    correctedGagliardoNirenbergRecordedIsTrue :
      correctedGagliardoNirenbergRecorded ≡ true

    vortexStretchingCubicBoundRecorded :
      Bool

    vortexStretchingCubicBoundRecordedIsTrue :
      vortexStretchingCubicBoundRecorded ≡ true

    youngGivesCubicEnstrophyODE :
      Bool

    youngGivesCubicEnstrophyODEIsTrue :
      youngGivesCubicEnstrophyODE ≡ true

    enstrophyODEPower :
      Nat

    enstrophyODEPowerIs3 :
      enstrophyODEPower ≡ enstrophyODEDegree

    estimateBlowupIsNotSolutionBlowup :
      Bool

    estimateBlowupIsNotSolutionBlowupIsTrue :
      estimateBlowupIsNotSolutionBlowup ≡ true

    serrinL4L4CriterionIdentified :
      Bool

    serrinL4L4CriterionIdentifiedIsTrue :
      serrinL4L4CriterionIdentified ≡ true

    serrinTimeExponent :
      Nat

    serrinTimeExponentIs4 :
      serrinTimeExponent ≡ requiredSerrinTimeExponent

    serrinSpaceExponent :
      Nat

    serrinSpaceExponentIs4 :
      serrinSpaceExponent ≡ requiredSerrinSpaceExponent

    classicalObstructionStartYear :
      Nat

    classicalObstructionStartYearIs1959 :
      classicalObstructionStartYear ≡ classicalReferenceStartYear

    classicalObstructionEndYear :
      Nat

    classicalObstructionEndYearIs1963 :
      classicalObstructionEndYear ≡ classicalReferenceEndYear

    vortexStretchingAbsorptionProved :
      Bool

    vortexStretchingAbsorptionProvedIsFalse :
      vortexStretchingAbsorptionProved ≡ false

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
      List NSLadyzhenskayaPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSLadyzhenskayaPromotion →
      ⊥

    summary :
      String

    summaryIsCanonical :
      summary ≡ nsLadyzhenskayaSummary

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ nsLadyzhenskayaBoundary

open NSLadyzhenskayaEnstrophyObstructionReceipt public

canonicalNSLadyzhenskayaEnstrophyObstructionReceipt :
  NSLadyzhenskayaEnstrophyObstructionReceipt
canonicalNSLadyzhenskayaEnstrophyObstructionReceipt =
  record
    { status =
        nsLadyzhenskayaObstructionRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; hingeReceipt =
        Hinge.canonicalNSEnstrophyClayHingeReceipt
    ; previousClayStillFalse =
        refl
    ; previousLiveHingeWasOpen =
        refl
    ; facts =
        canonicalNSLadyzhenskayaFacts
    ; factsAreCanonical =
        refl
    ; nonClaims =
        canonicalNSLadyzhenskayaNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; correctedGagliardoNirenbergRecorded =
        true
    ; correctedGagliardoNirenbergRecordedIsTrue =
        refl
    ; vortexStretchingCubicBoundRecorded =
        true
    ; vortexStretchingCubicBoundRecordedIsTrue =
        refl
    ; youngGivesCubicEnstrophyODE =
        true
    ; youngGivesCubicEnstrophyODEIsTrue =
        refl
    ; enstrophyODEPower =
        enstrophyODEDegree
    ; enstrophyODEPowerIs3 =
        refl
    ; estimateBlowupIsNotSolutionBlowup =
        true
    ; estimateBlowupIsNotSolutionBlowupIsTrue =
        refl
    ; serrinL4L4CriterionIdentified =
        true
    ; serrinL4L4CriterionIdentifiedIsTrue =
        refl
    ; serrinTimeExponent =
        requiredSerrinTimeExponent
    ; serrinTimeExponentIs4 =
        refl
    ; serrinSpaceExponent =
        requiredSerrinSpaceExponent
    ; serrinSpaceExponentIs4 =
        refl
    ; classicalObstructionStartYear =
        classicalReferenceStartYear
    ; classicalObstructionStartYearIs1959 =
        refl
    ; classicalObstructionEndYear =
        classicalReferenceEndYear
    ; classicalObstructionEndYearIs1963 =
        refl
    ; vortexStretchingAbsorptionProved =
        false
    ; vortexStretchingAbsorptionProvedIsFalse =
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
        nsLadyzhenskayaPromotionImpossibleHere
    ; summary =
        nsLadyzhenskayaSummary
    ; summaryIsCanonical =
        refl
    ; boundary =
        nsLadyzhenskayaBoundary
    ; boundaryIsCanonical =
        refl
    }

canonicalNSLadyzhenskayaKeepsClayFalse :
  clayNavierStokesPromoted
    canonicalNSLadyzhenskayaEnstrophyObstructionReceipt
  ≡
  false
canonicalNSLadyzhenskayaKeepsClayFalse =
  refl
