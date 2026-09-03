module DASHI.Moonshine.Base369Pointed729NestedNinetyBidiExact where

------------------------------------------------------------------------
-- NESTED BASE369 90 INSIDE 729
--
-- Base369PointedAppraisalFibreExact already constructs the pointed appraisal
-- carrier as eight noncentral addresses with Fine10 x SecondarySheet9, plus
-- one shared central SecondarySheet9.  The same product is the repository's
-- typed 10 x 9 multiplicity candidate.
--
-- This owner makes the recursion literal:
--
--   PointedAppraisal729
--      ~= (Fin 8 x TenByNineMultiplicity) + SecondarySheet9
--
-- and therefore exposes the exact structural shadow
--
--   729 = 8 * 90 + 9,
--   65610 = 729 * 90 = (8 * 90 + 9) * 90.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Foundations.Base369PointedAppraisalFibreExact as Pointed
import DASHI.Moonshine.Base369Monster3BMultiplicityTenByNineBidiExact as Ninety

NestedPointed729 : Set
NestedPointed729 =
  (Pointed.Noncentral8 × Ninety.TenByNineMultiplicity)
  ⊎ Pointed.SecondarySheet9

toNestedPointed729 : Pointed.PointedAppraisal729 → NestedPointed729
toNestedPointed729 (inj₁ address) =
  inj₁
    ( Pointed.noncentralPosition address
    , (Pointed.fineSector address , Pointed.secondaryPosition address)
    )
toNestedPointed729 (inj₂ address) =
  inj₂ (Pointed.centralSecondaryPosition address)

fromNestedPointed729 : NestedPointed729 → Pointed.PointedAppraisal729
fromNestedPointed729 (inj₁ (position , (fine , secondary))) =
  inj₁ (Pointed.noncentralFineAddress position fine secondary)
fromNestedPointed729 (inj₂ secondary) =
  inj₂ (Pointed.centralSharedAddress secondary)

fromAfterToNestedPointed729 :
  (state : Pointed.PointedAppraisal729) →
  fromNestedPointed729 (toNestedPointed729 state) ≡ state
fromAfterToNestedPointed729 (inj₁ (Pointed.noncentralFineAddress position fine secondary)) = refl
fromAfterToNestedPointed729 (inj₂ (Pointed.centralSharedAddress secondary)) = refl

toAfterFromNestedPointed729 :
  (state : NestedPointed729) →
  toNestedPointed729 (fromNestedPointed729 state) ≡ state
toAfterFromNestedPointed729 (inj₁ (position , (fine , secondary))) = refl
toAfterFromNestedPointed729 (inj₂ secondary) = refl

nestedPointedDimension : Nat
nestedPointedDimension = 8 * Ninety.tenByNineDimension + 9

nestedPointedDimensionIs729 : nestedPointedDimension ≡ 729
nestedPointedDimensionIs729 = refl

nestedZetaDimension : Nat
nestedZetaDimension = nestedPointedDimension * Ninety.tenByNineDimension

nestedZetaDimensionIs65610 : nestedZetaDimension ≡ 65610
nestedZetaDimensionIs65610 = refl

nestedThreePhaseBulkDimension : Nat
nestedThreePhaseBulkDimension = 3 * nestedZetaDimension

nestedThreePhaseBulkDimensionIs196830 :
  nestedThreePhaseBulkDimension ≡ 196830
nestedThreePhaseBulkDimensionIs196830 = refl

record NestedNinetyBoundary : Set where
  constructor nestedNinetyBoundary
  field
    pointed729CarrierEquivalenceConstructed : Bool
    sameTypedTenByNineSurfaceOccursInside729 : Bool
    outerMultiplicityTenByNineStillRequiresRecognition : Bool
    nestedArithmetic65610Generated : Bool
    nestedArithmetic196830Generated : Bool
    recursiveNinetyShapeAloneIdentifiesMonsterAction : Bool

canonicalNestedNinetyBoundary : NestedNinetyBoundary
canonicalNestedNinetyBoundary =
  nestedNinetyBoundary true true true true true false
