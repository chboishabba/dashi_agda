module DASHI.Physics.Closure.Chi2ToShiftPressureTransportCandidate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.Closure.Chi2CanonicalPoolObservationCandidate as CHI2POOL
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI

------------------------------------------------------------------------
-- W3 local chi2-to-shift-pressure transport candidate.
--
-- Boundary: local transport only, non-empirical, non-promoting, and not a
-- fixed-point landing or fixed-point empirical adequacy claim.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

chi2PoolToShiftPressurePoint :
  CHI2POOL.CanonicalChi2PoolCase →
  SPTI.ShiftPressurePoint
chi2PoolToShiftPressurePoint CHI2POOL.primaryPoolCase =
  SPTI.shiftStartPoint
chi2PoolToShiftPressurePoint CHI2POOL.secondaryPoolCase =
  SPTI.shiftNextPoint
chi2PoolToShiftPressurePoint CHI2POOL.tertiaryPoolCase =
  SPTI.shiftHeldExitPoint

primaryTransportLandsAtStart :
  chi2PoolToShiftPressurePoint CHI2POOL.primaryPoolCase
  ≡
  SPTI.shiftStartPoint
primaryTransportLandsAtStart = refl

secondaryTransportLandsAtNext :
  chi2PoolToShiftPressurePoint CHI2POOL.secondaryPoolCase
  ≡
  SPTI.shiftNextPoint
secondaryTransportLandsAtNext = refl

tertiaryTransportLandsAtHeld :
  chi2PoolToShiftPressurePoint CHI2POOL.tertiaryPoolCase
  ≡
  SPTI.shiftHeldExitPoint
tertiaryTransportLandsAtHeld = refl

primarySecondaryTransportDistinct :
  chi2PoolToShiftPressurePoint CHI2POOL.primaryPoolCase
  ≢
  chi2PoolToShiftPressurePoint CHI2POOL.secondaryPoolCase
primarySecondaryTransportDistinct ()

primaryTertiaryTransportDistinct :
  chi2PoolToShiftPressurePoint CHI2POOL.primaryPoolCase
  ≢
  chi2PoolToShiftPressurePoint CHI2POOL.tertiaryPoolCase
primaryTertiaryTransportDistinct ()

secondaryTertiaryTransportDistinct :
  chi2PoolToShiftPressurePoint CHI2POOL.secondaryPoolCase
  ≢
  chi2PoolToShiftPressurePoint CHI2POOL.tertiaryPoolCase
secondaryTertiaryTransportDistinct ()

chi2ToShiftPressureTransportNonconstant :
  chi2PoolToShiftPressurePoint CHI2POOL.primaryPoolCase
  ≢
  chi2PoolToShiftPressurePoint CHI2POOL.secondaryPoolCase
chi2ToShiftPressureTransportNonconstant =
  primarySecondaryTransportDistinct

chi2ToShiftPressureTransportPairwiseDistinct :
  (chi2PoolToShiftPressurePoint CHI2POOL.primaryPoolCase
    ≢
   chi2PoolToShiftPressurePoint CHI2POOL.secondaryPoolCase)
    ×
  ((chi2PoolToShiftPressurePoint CHI2POOL.primaryPoolCase
    ≢
    chi2PoolToShiftPressurePoint CHI2POOL.tertiaryPoolCase)
    ×
   (chi2PoolToShiftPressurePoint CHI2POOL.secondaryPoolCase
    ≢
    chi2PoolToShiftPressurePoint CHI2POOL.tertiaryPoolCase))
chi2ToShiftPressureTransportPairwiseDistinct =
  primarySecondaryTransportDistinct
  ,
  (primaryTertiaryTransportDistinct , secondaryTertiaryTransportDistinct)

data Chi2ToShiftPressureTransportBoundary : Set where
  localTransportOnly : Chi2ToShiftPressureTransportBoundary
  nonEmpiricalTransportOnly : Chi2ToShiftPressureTransportBoundary
  nonPromotingTransportOnly : Chi2ToShiftPressureTransportBoundary
  notFixedPointLandingClaim : Chi2ToShiftPressureTransportBoundary
  noFixedPointEmpiricalAdequacyClaim : Chi2ToShiftPressureTransportBoundary
  noAllCasesLandOnFixedPointClaim : Chi2ToShiftPressureTransportBoundary

record Chi2ToShiftPressureTransportCandidate : Set₁ where
  field
    sourceCandidate :
      CHI2POOL.Chi2CanonicalPoolObservationCandidate

    pressureTest :
      SPTI.shiftObservableSignaturePressureTest
        ≡
      SPTI.shiftObservableSignaturePressureTest

    transport :
      CHI2POOL.CanonicalChi2PoolCase →
      SPTI.ShiftPressurePoint

    primaryLandsAtStart :
      transport CHI2POOL.primaryPoolCase ≡ SPTI.shiftStartPoint

    secondaryLandsAtNext :
      transport CHI2POOL.secondaryPoolCase ≡ SPTI.shiftNextPoint

    tertiaryLandsAtHeld :
      transport CHI2POOL.tertiaryPoolCase ≡ SPTI.shiftHeldExitPoint

    primarySecondaryDistinct :
      transport CHI2POOL.primaryPoolCase
      ≢
      transport CHI2POOL.secondaryPoolCase

    primaryTertiaryDistinct :
      transport CHI2POOL.primaryPoolCase
      ≢
      transport CHI2POOL.tertiaryPoolCase

    secondaryTertiaryDistinct :
      transport CHI2POOL.secondaryPoolCase
      ≢
      transport CHI2POOL.tertiaryPoolCase

    boundary :
      List Chi2ToShiftPressureTransportBoundary

    boundaryStatement :
      List String

canonicalChi2ToShiftPressureTransportCandidate :
  Chi2ToShiftPressureTransportCandidate
canonicalChi2ToShiftPressureTransportCandidate =
  record
    { sourceCandidate =
        CHI2POOL.canonicalChi2PoolObservationCandidate
    ; pressureTest = refl
    ; transport =
        chi2PoolToShiftPressurePoint
    ; primaryLandsAtStart =
        primaryTransportLandsAtStart
    ; secondaryLandsAtNext =
        secondaryTransportLandsAtNext
    ; tertiaryLandsAtHeld =
        tertiaryTransportLandsAtHeld
    ; primarySecondaryDistinct =
        primarySecondaryTransportDistinct
    ; primaryTertiaryDistinct =
        primaryTertiaryTransportDistinct
    ; secondaryTertiaryDistinct =
        secondaryTertiaryTransportDistinct
    ; boundary =
        localTransportOnly
        ∷ nonEmpiricalTransportOnly
        ∷ nonPromotingTransportOnly
        ∷ notFixedPointLandingClaim
        ∷ noFixedPointEmpiricalAdequacyClaim
        ∷ noAllCasesLandOnFixedPointClaim
        ∷ []
    ; boundaryStatement =
        "local transport only"
        ∷ "non-empirical"
        ∷ "non-promoting"
        ∷ "not fixed-point landing"
        ∷ "no obs(fixedPoint)=empirical claim"
        ∷ "no all-cases-land-on-fixed-point claim"
        ∷ []
    }
