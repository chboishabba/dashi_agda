module DASHI.Physics.Moonshine.M24SplitNote where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Divisibility using (_∣_)
open import Data.Nat.Divisibility.Core using (divides)
open import Data.Nat using (_^_)

------------------------------------------------------------------------
-- Documentation note for the M24 split used in the Moonshine lane.
--
-- This file is intentionally documentation-only.  It records the pieces
-- that reduce in the local Nat fragment and keeps the remaining split
-- claim as an explicit residual hole.

data M24SplitNoteStatus : Set where
  documentationOnlyNoPromotion :
    M24SplitNoteStatus

data M24SplitResidualHole : Set where
  missingRepoNativeProofOfTheActualSplitTheorem :
    M24SplitResidualHole
  missingRepoNativeProofThat13DoesNotDivideM24 :
    M24SplitResidualHole

canonicalM24SplitResidualHoles :
  List M24SplitResidualHole
canonicalM24SplitResidualHoles =
  missingRepoNativeProofOfTheActualSplitTheorem
  ∷ missingRepoNativeProofThat13DoesNotDivideM24
  ∷ []

canonicalM24SplitTypedSurfaces :
  List String
canonicalM24SplitTypedSurfaces =
  "DASHI.Physics.Moonshine.DASHIMonsterVOAUniquenessReceipt"
  ∷ "DASHI.Physics.Moonshine.MoonshineTraceFamilySummary"
  ∷ "DASHI.Physics.Moonshine.MoonshineOrbitTraceSummary"
  ∷ "DASHI.Physics.Moonshine.DongLiMasonOrbifoldReceiptSurface"
  ∷ "DASHI.Physics.Moonshine.FiniteTwinedShellTrace"
  ∷ "DASHI.Physics.Moonshine.FiniteGradedShellSeries"
  ∷ []

canonicalM24SplitResidualHoleText :
  String
canonicalM24SplitResidualHoleText =
  "No repo-native proof of the M24 split theorem is constructed here; the local Nat fragment only computes the order value and the 7/11 divisibility witnesses, while the 13 non-divisibility claim remains a documentation hole."

m24OrderExpr : Nat
m24OrderExpr = 2 ^ 10 * 3 ^ 3 * 5 * 7 * 11 * 23

-- The fully reduced Nat value of the M24 order.
m24OrderValue : Nat
m24OrderValue = 244823040

m24OrderExprReduces : m24OrderExpr ≡ m24OrderValue
m24OrderExprReduces = refl

sevenTimesQ : Nat
sevenTimesQ = 34974720

elevenTimesQ : Nat
elevenTimesQ = 22256640

sevenDividesM24 : 7 ∣ m24OrderValue
sevenDividesM24 = divides sevenTimesQ refl

elevenDividesM24 : 11 ∣ m24OrderValue
elevenDividesM24 = divides elevenTimesQ refl

data M24SplitNotePromotionToken : Set where

record M24SplitNote : Set where
  field
    status :
      M24SplitNoteStatus

    m24Order :
      Nat

    m24OrderExpression :
      Nat

    m24OrderExpressionReduces :
      m24OrderExpression ≡ m24Order

    sevenDivisibility :
      7 ∣ m24Order

    elevenDivisibility :
      11 ∣ m24Order

    splitPromoted :
      Bool

    splitPromotedIsFalse :
      splitPromoted ≡ false

    currentTypedSurfaces :
      List String

    currentTypedSurfacesAreCanonical :
      currentTypedSurfaces ≡ canonicalM24SplitTypedSurfaces

    residualHoleText :
      String

    residualHoleTextIsCanonical :
      residualHoleText ≡ canonicalM24SplitResidualHoleText

    residualHoles :
      List M24SplitResidualHole

    residualHolesAreCanonical :
      residualHoles ≡ canonicalM24SplitResidualHoles

    futurePromotionBlocked :
      M24SplitNotePromotionToken →
      ⊥

canonicalM24SplitNote : M24SplitNote
canonicalM24SplitNote = record
  { status =
      documentationOnlyNoPromotion
  ; m24Order =
      m24OrderValue
  ; m24OrderExpression =
      m24OrderExpr
  ; m24OrderExpressionReduces =
      m24OrderExprReduces
  ; sevenDivisibility =
      sevenDividesM24
  ; elevenDivisibility =
      elevenDividesM24
  ; splitPromoted =
      false
  ; splitPromotedIsFalse =
      refl
  ; currentTypedSurfaces =
      canonicalM24SplitTypedSurfaces
  ; currentTypedSurfacesAreCanonical =
      refl
  ; residualHoleText =
      canonicalM24SplitResidualHoleText
  ; residualHoleTextIsCanonical =
      refl
  ; residualHoles =
      canonicalM24SplitResidualHoles
  ; residualHolesAreCanonical =
      refl
  ; futurePromotionBlocked =
      λ ()
  }
