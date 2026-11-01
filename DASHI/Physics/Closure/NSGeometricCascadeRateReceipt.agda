module DASHI.Physics.Closure.NSGeometricCascadeRateReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Navier-Stokes geometric cascade-rate receipt.
--
-- This receipt records the A5 cascade-rate calculation:
--
--   R_j = e_j*/e_(j-1) = C0^2 p^(11/4 - 2j)/nu^2.
--
-- At the cutoff successor j = j_nu + 1, using
--
--   p^(2 j_nu) approx (C0/nu)^2 p^(11/4),
--
-- the rate is approximately p^-2 and the explicit nu-dependence cancels.
-- The table records the resulting geometric ratios and tail sums for
-- p = 2,3,7.  This is only a geometric-rate receipt; it creates no Clay
-- Navier-Stokes or global-regularity promotion.

data NSGeometricCascadeRateStatus : Set where
  cascadeRateFormulaRecorded :
    NSGeometricCascadeRateStatus

  cutoffSuccessorCancellationRecorded :
    NSGeometricCascadeRateStatus

  nuIndependentRateRecorded :
    NSGeometricCascadeRateStatus

  geometricTailConvergenceRecorded :
    NSGeometricCascadeRateStatus

  explicitRateTableRecorded :
    NSGeometricCascadeRateStatus

  noClayOrGlobalPromotion :
    NSGeometricCascadeRateStatus

canonicalNSGeometricCascadeRateStatus :
  List NSGeometricCascadeRateStatus
canonicalNSGeometricCascadeRateStatus =
  cascadeRateFormulaRecorded
  ∷ cutoffSuccessorCancellationRecorded
  ∷ nuIndependentRateRecorded
  ∷ geometricTailConvergenceRecorded
  ∷ explicitRateTableRecorded
  ∷ noClayOrGlobalPromotion
  ∷ []

data CascadeRateTableEntry : Set where
  p2Rate025Sum0333 :
    CascadeRateTableEntry

  p3Rate011Sum0125 :
    CascadeRateTableEntry

  p7Rate002 :
    CascadeRateTableEntry

canonicalExplicitRateTable :
  List CascadeRateTableEntry
canonicalExplicitRateTable =
  p2Rate025Sum0333
  ∷ p3Rate011Sum0125
  ∷ p7Rate002
  ∷ []

data NSGeometricCascadeRatePromotion : Set where

nsGeometricCascadeRatePromotionImpossibleHere :
  NSGeometricCascadeRatePromotion →
  ⊥
nsGeometricCascadeRatePromotionImpossibleHere ()

cascadeRateFormula : String
cascadeRateFormula =
  "R_j = e_j*/e_(j-1) = C0^2 p^(11/4-2j)/nu^2"

cutoffSuccessorCancellationFormula : String
cutoffSuccessorCancellationFormula =
  "at j=j_nu+1, p^(2j_nu) approx (C0/nu)^2 p^(11/4), so R approx p^-2"

geometricRateTableText : String
geometricRateTableText =
  "p=2: rate 0.25, geometric sum 0.333; p=3: rate 0.11, geometric sum 0.125; p=7: rate 0.02"

nsGeometricCascadeRateStatement : String
nsGeometricCascadeRateStatement =
  "The cascade rate R_j = e_j*/e_(j-1) = C0^2 p^(11/4-2j)/nu^2 becomes approximately p^-2 at j=j_nu+1 after using p^(2j_nu) approx (C0/nu)^2 p^(11/4), hence the cutoff-successor rate is nu-independent.  The explicit table records p=2 -> 0.25 with geometric sum 0.333, p=3 -> 0.11 with sum 0.125, and p=7 -> 0.02.  No Clay or global regularity promotion follows."

record NSGeometricCascadeRateReceipt : Setω where
  field
    status :
      List NSGeometricCascadeRateStatus

    statusIsCanonical :
      status ≡ canonicalNSGeometricCascadeRateStatus

    cascadeRate :
      String

    cascadeRateIsCanonical :
      cascadeRate ≡ cascadeRateFormula

    cutoffSuccessorCancellation :
      String

    cutoffSuccessorCancellationIsCanonical :
      cutoffSuccessorCancellation ≡ cutoffSuccessorCancellationFormula

    cascadeRateNuIndependent :
      Bool

    cascadeRateNuIndependentIsTrue :
      cascadeRateNuIndependent ≡ true

    geometricSumConverges :
      Bool

    geometricSumConvergesIsTrue :
      geometricSumConverges ≡ true

    explicitRateTable :
      List CascadeRateTableEntry

    explicitRateTableIsCanonical :
      explicitRateTable ≡ canonicalExplicitRateTable

    explicitRateTableText :
      String

    explicitRateTableTextIsCanonical :
      explicitRateTableText ≡ geometricRateTableText

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    promotionFlags :
      List NSGeometricCascadeRatePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ nsGeometricCascadeRateStatement

    receiptBoundary :
      List String

open NSGeometricCascadeRateReceipt public

canonicalNSGeometricCascadeRateReceipt :
  NSGeometricCascadeRateReceipt
canonicalNSGeometricCascadeRateReceipt =
  record
    { status =
        canonicalNSGeometricCascadeRateStatus
    ; statusIsCanonical =
        refl
    ; cascadeRate =
        cascadeRateFormula
    ; cascadeRateIsCanonical =
        refl
    ; cutoffSuccessorCancellation =
        cutoffSuccessorCancellationFormula
    ; cutoffSuccessorCancellationIsCanonical =
        refl
    ; cascadeRateNuIndependent =
        true
    ; cascadeRateNuIndependentIsTrue =
        refl
    ; geometricSumConverges =
        true
    ; geometricSumConvergesIsTrue =
        refl
    ; explicitRateTable =
        canonicalExplicitRateTable
    ; explicitRateTableIsCanonical =
        refl
    ; explicitRateTableText =
        geometricRateTableText
    ; explicitRateTableTextIsCanonical =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        nsGeometricCascadeRateStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Records only the geometric cascade-rate calculation"
        ∷ "At j=j_nu+1 the cascade ratio is approximately p^-2"
        ∷ "The cutoff-successor rate is independent of nu"
        ∷ "Explicit table: p=2 -> 0.25 and sum 0.333; p=3 -> 0.11 and sum 0.125; p=7 -> 0.02"
        ∷ "No Clay Navier-Stokes or global regularity promotion is made"
        ∷ []
    }

cascadeRateNuIndependentTrue :
  cascadeRateNuIndependent canonicalNSGeometricCascadeRateReceipt
    ≡
    true
cascadeRateNuIndependentTrue =
  refl

geometricSumConvergesTrue :
  geometricSumConverges canonicalNSGeometricCascadeRateReceipt
    ≡
    true
geometricSumConvergesTrue =
  refl

clayNavierStokesPromotedFalse :
  clayNavierStokesPromoted canonicalNSGeometricCascadeRateReceipt
    ≡
    false
clayNavierStokesPromotedFalse =
  refl

globalRegularityPromotedFalse :
  globalRegularityPromoted canonicalNSGeometricCascadeRateReceipt
    ≡
    false
globalRegularityPromotedFalse =
  refl
