module DASHI.Physics.Closure.Chi2CanonicalPoolObservationCandidate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.Closure.Chi2NonForgettingSameSurfaceObstruction as OBS
open import DASHI.Physics.Closure.Validation.Chi2BoundaryShiftLibrary as LIB

------------------------------------------------------------------------
-- W3 chi2 canonical-pool observation candidate.
--
-- This is intentionally only a local surface over the three canonical chi2
-- pool cases.  It is non-empirical, non-promoting, and does not repair the
-- same-Nat-defect obstruction recorded in
-- `Chi2NonForgettingSameSurfaceObstruction`.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

data CanonicalChi2PoolCase : Set where
  primaryPoolCase : CanonicalChi2PoolCase
  secondaryPoolCase : CanonicalChi2PoolCase
  tertiaryPoolCase : CanonicalChi2PoolCase

poolCaseToBoundaryCase :
  CanonicalChi2PoolCase →
  LIB.Chi2BoundaryCase
poolCaseToBoundaryCase primaryPoolCase = OBS.primaryCase
poolCaseToBoundaryCase secondaryPoolCase = OBS.secondaryCase
poolCaseToBoundaryCase tertiaryPoolCase = OBS.tertiaryCase

chi2PoolObservation :
  CanonicalChi2PoolCase →
  Nat
chi2PoolObservation primaryPoolCase = zero
chi2PoolObservation secondaryPoolCase = suc zero
chi2PoolObservation tertiaryPoolCase = suc (suc zero)

primarySecondaryObservationDistinct :
  chi2PoolObservation primaryPoolCase
    ≢
  chi2PoolObservation secondaryPoolCase
primarySecondaryObservationDistinct ()

primaryTertiaryObservationDistinct :
  chi2PoolObservation primaryPoolCase
    ≢
  chi2PoolObservation tertiaryPoolCase
primaryTertiaryObservationDistinct ()

secondaryTertiaryObservationDistinct :
  chi2PoolObservation secondaryPoolCase
    ≢
  chi2PoolObservation tertiaryPoolCase
secondaryTertiaryObservationDistinct ()

chi2PoolObservationNonconstant :
  chi2PoolObservation primaryPoolCase
    ≢
  chi2PoolObservation secondaryPoolCase
chi2PoolObservationNonconstant =
  primarySecondaryObservationDistinct

data Chi2CanonicalPoolBoundary : Set where
  localCanonicalPoolOnly : Chi2CanonicalPoolBoundary
  nonEmpiricalObservationOnly : Chi2CanonicalPoolBoundary
  nonPromotingObservationOnly : Chi2CanonicalPoolBoundary
  noFixedPointEmpiricalAdequacyClaim : Chi2CanonicalPoolBoundary

data Chi2CanonicalPoolClosureGap : Set where
  missingSameSurfaceTransportLaw : Chi2CanonicalPoolClosureGap
  missingEmpiricalObservationTarget : Chi2CanonicalPoolClosureGap
  missingPromotionBridge : Chi2CanonicalPoolClosureGap
  sameNatDefectObstructionStillApplies : Chi2CanonicalPoolClosureGap

record Chi2CanonicalPoolObservationCandidate : Set₁ where
  field
    carrier : Set
    boundaryCase : carrier → LIB.Chi2BoundaryCase
    observation : carrier → Nat
    primaryToken : carrier
    secondaryToken : carrier
    tertiaryToken : carrier
    primaryObservation :
      observation primaryToken ≡ zero
    secondaryObservation :
      observation secondaryToken ≡ suc zero
    tertiaryObservation :
      observation tertiaryToken ≡ suc (suc zero)
    primarySecondaryDistinct :
      observation primaryToken ≢ observation secondaryToken
    primaryTertiaryDistinct :
      observation primaryToken ≢ observation tertiaryToken
    secondaryTertiaryDistinct :
      observation secondaryToken ≢ observation tertiaryToken
    boundary :
      List Chi2CanonicalPoolBoundary
    remainingW3ClosureGaps :
      List Chi2CanonicalPoolClosureGap
    obstructionStillInForce :
      OBS.Chi2NonForgettingSameSurfaceObstruction
    boundaryStatement :
      List String

canonicalChi2PoolObservationCandidate :
  Chi2CanonicalPoolObservationCandidate
canonicalChi2PoolObservationCandidate =
  record
    { carrier = CanonicalChi2PoolCase
    ; boundaryCase = poolCaseToBoundaryCase
    ; observation = chi2PoolObservation
    ; primaryToken = primaryPoolCase
    ; secondaryToken = secondaryPoolCase
    ; tertiaryToken = tertiaryPoolCase
    ; primaryObservation = refl
    ; secondaryObservation = refl
    ; tertiaryObservation = refl
    ; primarySecondaryDistinct = primarySecondaryObservationDistinct
    ; primaryTertiaryDistinct = primaryTertiaryObservationDistinct
    ; secondaryTertiaryDistinct = secondaryTertiaryObservationDistinct
    ; boundary =
        localCanonicalPoolOnly
        ∷ nonEmpiricalObservationOnly
        ∷ nonPromotingObservationOnly
        ∷ noFixedPointEmpiricalAdequacyClaim
        ∷ []
    ; remainingW3ClosureGaps =
        missingSameSurfaceTransportLaw
        ∷ missingEmpiricalObservationTarget
        ∷ missingPromotionBridge
        ∷ sameNatDefectObstructionStillApplies
        ∷ []
    ; obstructionStillInForce =
        OBS.canonicalChi2NonForgettingSameSurfaceObstruction
    ; boundaryStatement =
        "Local canonical chi2-pool discriminator only"
        ∷ "Not an empirical observation target"
        ∷ "Not a promotion bridge"
        ∷ "No claim that obs(fixedPoint) is empirical"
        ∷ []
    }

canonicalPrimarySecondaryDistinguished :
  chi2PoolObservation primaryPoolCase
    ≢
  chi2PoolObservation secondaryPoolCase
canonicalPrimarySecondaryDistinguished =
  primarySecondaryObservationDistinct

canonicalPairwiseDistinguished :
  (chi2PoolObservation primaryPoolCase ≢ chi2PoolObservation secondaryPoolCase)
    ×
  ((chi2PoolObservation primaryPoolCase ≢ chi2PoolObservation tertiaryPoolCase)
    ×
   (chi2PoolObservation secondaryPoolCase ≢ chi2PoolObservation tertiaryPoolCase))
canonicalPairwiseDistinguished =
  primarySecondaryObservationDistinct
  ,
  (primaryTertiaryObservationDistinct , secondaryTertiaryObservationDistinct)
