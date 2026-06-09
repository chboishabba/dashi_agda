module DASHI.Physics.Closure.Deg23ShimuraApproachReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Deg23DirectIsogenyReceipt as Direct
import DASHI.Physics.Closure.HeckeCorrOnX021Receipt as X021

------------------------------------------------------------------------
-- Correct target for a deg23 derivation.

data Deg23ShimuraStatus : Set where
  deg23ShimuraApproachNamed :
    Deg23ShimuraStatus

data Deg23ShimuraBlocker : Set where
  hilbertModularSurfaceVolumeNotComputed :
    Deg23ShimuraBlocker

  cmPeriodIntegralNotFormalised :
    Deg23ShimuraBlocker

  biquadraticCMComparisonNotInCarrier :
    Deg23ShimuraBlocker

canonicalDeg23ShimuraBlockers : List Deg23ShimuraBlocker
canonicalDeg23ShimuraBlockers =
  hilbertModularSurfaceVolumeNotComputed
  ∷ cmPeriodIntegralNotFormalised
  ∷ biquadraticCMComparisonNotInCarrier
  ∷ []

data Deg23ShimuraPromotion : Set where

deg23ShimuraPromotionImpossibleHere :
  Deg23ShimuraPromotion →
  ⊥
deg23ShimuraPromotionImpossibleHere ()

record Deg23ShimuraApproachReceipt : Set where
  field
    status :
      Deg23ShimuraStatus

    directAudit :
      Direct.Deg23DirectIsogenyReceipt

    directAuditIsCanonical :
      directAudit ≡ Direct.canonicalDeg23DirectIsogenyReceipt

    x021Audit :
      X021.HeckeCorrOnX021Receipt

    x021AuditIsCanonical :
      x021Audit ≡ X021.canonicalHeckeCorrOnX021Receipt

    cmPair :
      String

    biquadraticCMField :
      String

    realQuadraticSubfield :
      String

    candidateModuliObject :
      String

    candidatePeriodObject :
      String

    deg23FromHilbertModularSurface :
      Bool

    deg23FromHilbertModularSurfaceIsCandidate :
      deg23FromHilbertModularSurface ≡ true

    deg23ShimuraDerivationBlocked :
      Bool

    deg23ShimuraDerivationBlockedIsTrue :
      deg23ShimuraDerivationBlocked ≡ true

    deg23DerivedHere :
      Bool

    deg23DerivedHereIsFalse :
      deg23DerivedHere ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List Deg23ShimuraBlocker

    blockersAreCanonical :
      blockers ≡ canonicalDeg23ShimuraBlockers

    promotionFlags :
      List Deg23ShimuraPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open Deg23ShimuraApproachReceipt public

canonicalDeg23ShimuraApproachReceipt :
  Deg23ShimuraApproachReceipt
canonicalDeg23ShimuraApproachReceipt =
  record
    { status =
        deg23ShimuraApproachNamed
    ; directAudit =
        Direct.canonicalDeg23DirectIsogenyReceipt
    ; directAuditIsCanonical =
        refl
    ; x021Audit =
        X021.canonicalHeckeCorrOnX021Receipt
    ; x021AuditIsCanonical =
        refl
    ; cmPair =
        "D=-3 and D=-7"
    ; biquadraticCMField =
        "Q(sqrt(-3),sqrt(-7))"
    ; realQuadraticSubfield =
        "Q(sqrt(21))"
    ; candidateModuliObject =
        "Hilbert/Shimura surface for pairs of CM elliptic curves of the two CM types"
    ; candidatePeriodObject =
        "period of the abelian surface with CM by Z[omega] x Z[(1+sqrt(-7))/2]"
    ; deg23FromHilbertModularSurface =
        true
    ; deg23FromHilbertModularSurfaceIsCandidate =
        refl
    ; deg23ShimuraDerivationBlocked =
        true
    ; deg23ShimuraDerivationBlockedIsTrue =
        refl
    ; deg23DerivedHere =
        false
    ; deg23DerivedHereIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalDeg23ShimuraBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "This receipt names the candidate mathematical home for deg23"
        ∷ "The Hilbert modular period/volume computation is not performed here"
        ∷ "The old deg23=14 surface remains diagnostic only"
        ∷ []
    }

deg23ShimuraDoesNotPromoteCKM :
  physicalCKMPromoted canonicalDeg23ShimuraApproachReceipt ≡ false
deg23ShimuraDoesNotPromoteCKM =
  refl

