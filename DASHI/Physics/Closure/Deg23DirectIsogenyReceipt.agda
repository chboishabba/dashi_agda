module DASHI.Physics.Closure.Deg23DirectIsogenyReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- deg23 direct-isogeny audit.
--
-- This receipt records that the historical deg23=14 surface is a useful
-- diagnostic pattern, not a derived isogeny degree.

data Deg23DirectStatus : Set where
  deg23DirectIsogenyAuditRecorded :
    Deg23DirectStatus

data Deg23DirectBlocker : Set where
  pointCountSumIsPatternMatched :
    Deg23DirectBlocker

  noDirectRationalIsogenyBetweenDifferentCMFields :
    Deg23DirectBlocker

  residualIsStructuralNotPerturbative :
    Deg23DirectBlocker

  needsCMPeriodOrShimuraDerivation :
    Deg23DirectBlocker

canonicalDeg23DirectBlockers : List Deg23DirectBlocker
canonicalDeg23DirectBlockers =
  pointCountSumIsPatternMatched
  ∷ noDirectRationalIsogenyBetweenDifferentCMFields
  ∷ residualIsStructuralNotPerturbative
  ∷ needsCMPeriodOrShimuraDerivation
  ∷ []

data Deg23DirectPromotion : Set where

deg23DirectPromotionImpossibleHere :
  Deg23DirectPromotion →
  ⊥
deg23DirectPromotionImpossibleHere ()

record Deg23DirectIsogenyReceipt : Set where
  field
    status :
      Deg23DirectStatus

    p3Discriminant :
      String

    p5Discriminant :
      String

    legacyFormula :
      String

    legacyDeg23 :
      Nat

    eF5PointCount :
      Nat

    eF7PointCount :
      Nat

    deg12Comparison :
      String

    deg23FormulaUnderived :
      Bool

    deg23FormulaUnderivedIsTrue :
      deg23FormulaUnderived ≡ true

    deg23ResidualIsStructuralNotPerturbative :
      Bool

    deg23ResidualIsStructuralNotPerturbativeIsTrue :
      deg23ResidualIsStructuralNotPerturbative ≡ true

    deg23NeedsNewDerivation :
      Bool

    deg23NeedsNewDerivationIsTrue :
      deg23NeedsNewDerivation ≡ true

    correctDerivationTarget :
      String

    directPhysicalVcbDerived :
      Bool

    directPhysicalVcbDerivedIsFalse :
      directPhysicalVcbDerived ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List Deg23DirectBlocker

    blockersAreCanonical :
      blockers ≡ canonicalDeg23DirectBlockers

    promotionFlags :
      List Deg23DirectPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open Deg23DirectIsogenyReceipt public

canonicalDeg23DirectIsogenyReceipt :
  Deg23DirectIsogenyReceipt
canonicalDeg23DirectIsogenyReceipt =
  record
    { status =
        deg23DirectIsogenyAuditRecorded
    ; p3Discriminant =
        "D=-3, j=0, CM by Z[omega]"
    ; p5Discriminant =
        "D=-7, j=-3375, CM by Z[(1+sqrt(-7))/2]"
    ; legacyFormula =
        "deg23 = |E(F_5)| + |E(F_7)|"
    ; legacyDeg23 =
        14
    ; eF5PointCount =
        6
    ; eF7PointCount =
        8
    ; deg12Comparison =
        "deg12 has a volume/period receipt; deg23=14 does not yet have the analogous derivation"
    ; deg23FormulaUnderived =
        true
    ; deg23FormulaUnderivedIsTrue =
        refl
    ; deg23ResidualIsStructuralNotPerturbative =
        true
    ; deg23ResidualIsStructuralNotPerturbativeIsTrue =
        refl
    ; deg23NeedsNewDerivation =
        true
    ; deg23NeedsNewDerivationIsTrue =
        refl
    ; correctDerivationTarget =
        "CM period integral or Shimura/Hilbert modular surface for the D=-3 and D=-7 pair"
    ; directPhysicalVcbDerived =
        false
    ; directPhysicalVcbDerivedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalDeg23DirectBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The deg23=14 point-count formula is retained only as a diagnostic surface"
        ∷ "The residual is not treated as a small correction to a proved formula"
        ∷ "No physical Vcb or CKM promotion is asserted"
        ∷ []
    }

deg23DirectDoesNotPromoteCKM :
  physicalCKMPromoted canonicalDeg23DirectIsogenyReceipt ≡ false
deg23DirectDoesNotPromoteCKM =
  refl

