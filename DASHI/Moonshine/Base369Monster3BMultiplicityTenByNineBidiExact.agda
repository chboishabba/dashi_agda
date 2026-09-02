module DASHI.Moonshine.Base369Monster3BMultiplicityTenByNineBidiExact where

------------------------------------------------------------------------
-- SAME-ACTION BIDI: literal Fin 90 multiplicity <-> Base369 10 x 9 surface
--
-- The repository already owns a typed Base369 pointed-appraisal decomposition
-- with
--
--   Fine10 = Fin 10,
--   SecondarySheet9 = Fin 9,
--   fineRelationalSurface90 = 10 * 9 = 90.
--
-- Separately, actual Monster 3B zeta recognition owns a literal Fin 90
-- multiplicity coordinate.  This owner makes the intended comparison precise:
-- the two 90-carriers may be identified only by a two-sided recognition that
-- transports the SAME actual multiplicity/inertia action.
--
-- It also puts the existing 12 + 78 recognition on that exact same action, so
-- 10 x 9 and 12 + 78 become two coordinate systems on one multiplicity object,
-- not two unrelated degree-90 representations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)
open import Data.Fin.Base using (Fin)
open import Data.Product using (_×_)

import DASHI.Foundations.Base369PointedAppraisalFibreExact as Pointed
import DASHI.Moonshine.Base369Monster3BActualActionRecognitionBidiExact as Action
import DASHI.Moonshine.Base369Monster3BMultiplicityInertiaTwelveSeventyEightBidiExact as Actual

------------------------------------------------------------------------
-- 1. Reuse the existing typed Base369 10 x 9 factors literally.
------------------------------------------------------------------------

TenByNineMultiplicity : Set
TenByNineMultiplicity = Pointed.Fine10 × Pointed.SecondarySheet9

tenByNineDimension : Nat
tenByNineDimension = 10 * 9

tenByNineDimensionIsNinety : tenByNineDimension ≡ 90
tenByNineDimensionIsNinety = Pointed.fineRelationalSurface90Exact

heisenbergTimesTenByNineDimension : Nat
heisenbergTimesTenByNineDimension = 729 * tenByNineDimension

heisenbergTimesTenByNineIs65610 :
  heisenbergTimesTenByNineDimension ≡ 65610
heisenbergTimesTenByNineIs65610 = refl

threePhaseTenByNineBulkDimension : Nat
threePhaseTenByNineBulkDimension = 3 * heisenbergTimesTenByNineDimension

threePhaseTenByNineBulkIs196830 :
  threePhaseTenByNineBulkDimension ≡ 196830
threePhaseTenByNineBulkIs196830 = refl

------------------------------------------------------------------------
-- 2. Attach that exact 10 x 9 surface to the literal Fin 90 multiplicity
--    coordinate and transport the same actual inertia action.
------------------------------------------------------------------------

record ActualMultiplicityTenByNineAttachment
    {source : Action.ActualMonster3BActionRecognition}
    (inertiaAttachment : Actual.ActualMultiplicityInertiaAttachment source)
    : Set₁ where
  field
    toTenByNine : Fin 90 → TenByNineMultiplicity
    fromTenByNine : TenByNineMultiplicity → Fin 90

    fromAfterTo :
      (multiplicity : Fin 90) →
      fromTenByNine (toTenByNine multiplicity) ≡ multiplicity

    toAfterFrom :
      (surface : TenByNineMultiplicity) →
      toTenByNine (fromTenByNine surface) ≡ surface

    tenByNineAct :
      Actual.MultiplicityInertia inertiaAttachment →
      TenByNineMultiplicity → TenByNineMultiplicity

    sameActualMultiplicityAction :
      (inertia : Actual.MultiplicityInertia inertiaAttachment) →
      (multiplicity : Fin 90) →
      toTenByNine
        (Actual.multiplicityAct inertiaAttachment inertia multiplicity)
      ≡ tenByNineAct inertia (toTenByNine multiplicity)

open ActualMultiplicityTenByNineAttachment public

------------------------------------------------------------------------
-- 3. The existing 12 + 78 split and the 10 x 9 chart can now be required on
--    exactly one ActualMultiplicityInertiaAttachment.
------------------------------------------------------------------------

record ActualMultiplicityDualNinetyCoordinateAttachment
    (source : Action.ActualMonster3BActionRecognition) : Set₁ where
  field
    twelveSeventyEight :
      Actual.ActualMultiplicityTwelveSeventyEightAttachment source

    tenByNine :
      ActualMultiplicityTenByNineAttachment
        (Actual.inertiaAttachment twelveSeventyEight)

open ActualMultiplicityDualNinetyCoordinateAttachment public

------------------------------------------------------------------------
-- 4. The same literal 90 multiplicity therefore feeds the same 729 factor.
--    This is the exact arithmetic shadow of the desired action-level picture:
--
--       729 x (10 x 9) = 729 x 90 = 65610,
--       3 x 729 x (10 x 9) = 196830.
--
-- The arithmetic is generated immediately.  What remains scientific is the
-- two-sided/action recognition Fin 90 <-> Fine10 x SecondarySheet9.
------------------------------------------------------------------------

record MultiplicityTenByNineBoundary : Set where
  constructor multiplicityTenByNineBoundary
  field
    base369TenByNineSurfaceAlreadyOwned : Bool
    literalFin90MultiplicityAlreadyOwned : Bool
    tenByNineDimensionMatchesNinety : Bool
    tenByNineTimes729Matches65610 : Bool
    threePhaseTenByNineMatches196830 : Bool
    twoSidedCarrierRecognitionRequired : Bool
    sameActualMultiplicityActionRequired : Bool
    twelvePlusSeventyEightCanShareSameMultiplicityAction : Bool
    dimensionNinetyAlonePromotesRecognition : Bool
    actualTenByNineRecognitionInhabitedHere : Bool

canonicalMultiplicityTenByNineBoundary : MultiplicityTenByNineBoundary
canonicalMultiplicityTenByNineBoundary =
  multiplicityTenByNineBoundary
    true true true true true true true true false false
