module DASHI.Physics.Closure.NSTriadKNR571PhysicalM2DissipationFoldExact where

------------------------------------------------------------------------
-- PERIODIC B / LITERAL R571 M2 -> PHYSICAL DISSIPATION FOLD
--
-- This sits one level below the R568 bridge.  The finite summation theorem is
-- already cardinality-free; the only additional algebra needed at fixed
-- cutoff/time is to identify the sum of literal sample dissipation
-- contributions with (or below) the physical Galerkin dissipation density.
--
-- No fibre cardinality enters this theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNR571PhysicalSecondMomentSummationExact as SumPay

record LiteralR571DissipationFold : Set₁ where
  field
    familyPayment : SumPay.PhysicalSecondMomentFamilyPayment
    physicalDissipationDensity : ℚ

    literalDissipationFold :
      SumPay.physicalDissipationSum familyPayment
      ≤ physicalDissipationDensity

open LiteralR571DissipationFold public

literalR571M2BelowPhysicalDissipation :
  (P : LiteralR571DissipationFold) →
  SumPay.physicalSecondMomentSum (familyPayment P)
  ≤ physicalDissipationDensity P
literalR571M2BelowPhysicalDissipation P =
  ℚP.≤-trans
    (SumPay.finitePhysicalSecondMomentPayment (familyPayment P))
    (literalDissipationFold P)

record ExactLiteralR571DissipationFold : Set₁ where
  field
    familyPayment : SumPay.PhysicalSecondMomentFamilyPayment
    physicalDissipationDensity : ℚ
    literalDissipationFoldExact :
      SumPay.physicalDissipationSum familyPayment
      ≡ physicalDissipationDensity

open ExactLiteralR571DissipationFold public

exactFoldToPayment :
  ExactLiteralR571DissipationFold →
  LiteralR571DissipationFold
exactFoldToPayment P = record
  { familyPayment = ExactLiteralR571DissipationFold.familyPayment P
  ; physicalDissipationDensity =
      ExactLiteralR571DissipationFold.physicalDissipationDensity P
  ; literalDissipationFold =
      subst
        (SumPay.physicalDissipationSum
          (ExactLiteralR571DissipationFold.familyPayment P) ≤_)
        (ExactLiteralR571DissipationFold.literalDissipationFoldExact P)
        ℚP.≤-refl
  }

exactLiteralR571M2BelowPhysicalDissipation :
  (P : ExactLiteralR571DissipationFold) →
  SumPay.physicalSecondMomentSum
    (ExactLiteralR571DissipationFold.familyPayment P)
  ≤ ExactLiteralR571DissipationFold.physicalDissipationDensity P
exactLiteralR571M2BelowPhysicalDissipation P =
  literalR571M2BelowPhysicalDissipation (exactFoldToPayment P)

cardinalityFreeFiniteFoldClosed : Bool
cardinalityFreeFiniteFoldClosed = true

samplewisePhysicalPaymentStillAnalytic : Bool
samplewisePhysicalPaymentStillAnalytic = true

literalFoldIntoGalerkinDissipationStillAnalytic : Bool
literalFoldIntoGalerkinDissipationStillAnalytic = true

clayPromotion : Bool
clayPromotion = false

cardinalityFreeFiniteFoldClosedIsTrue :
  cardinalityFreeFiniteFoldClosed ≡ true
cardinalityFreeFiniteFoldClosedIsTrue = refl
