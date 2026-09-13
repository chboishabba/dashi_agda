module DASHI.Physics.Closure.NSTriadKNCommonInitialDatumCriticalCeilingNoGoRound511Exact where

------------------------------------------------------------------------
-- ROUND511 / COMMON INITIAL DATUM DOES NOT CREATE A CRITICAL CEILING
--
-- R240 proves all cutoffs use one common initial Fourier datum on their listed
-- modes.  R421 separately consumes a cutoff-uniform bound on the `initialCritical`
-- scalar of its critical slice.  Those are not the same capability.
--
-- The countermodel below proves the logical non-implication directly: a model
-- can carry a common-initial-datum receipt while having no critical-ceiling
-- receipt at all.  Therefore proof search must obtain a same-object realization
-- of `initialCritical` as a literal initial-data functional, together with a
-- bound for that functional; it may not promote R240's common-datum field by
-- name alone.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNIntrospectiveCriticalProductionSchedulerRound510Exact as R510

data Empty : Set where

record InitialDatumCapabilityModel : Set₁ where
  field
    CommonInitialDatumReceipt : Set
    UniformInitialCriticalCeilingReceipt : Set

open InitialDatumCapabilityModel public

commonDatumWithoutCeiling : InitialDatumCapabilityModel
commonDatumWithoutCeiling = record
  { CommonInitialDatumReceipt = ⊤
  ; UniformInitialCriticalCeilingReceipt = Empty
  }

CommonDatumImpliesCeilingForEveryModel : Set₁
CommonDatumImpliesCeilingForEveryModel =
  (M : InitialDatumCapabilityModel) →
  CommonInitialDatumReceipt M →
  UniformInitialCriticalCeilingReceipt M

commonInitialDatumDoesNotCreateCriticalCeiling :
  CommonDatumImpliesCeilingForEveryModel → Empty
commonInitialDatumDoesNotCreateCriticalCeiling promote =
  promote commonDatumWithoutCeiling tt

round511Round240CommonInitialDatumOwned : Bool
round511Round240CommonInitialDatumOwned =
  R240.round240CorrectedTrajectoryOwnsCommonInitialDatum

round511CommonInitialDatumAlonePaysCriticalCeiling : Bool
round511CommonInitialDatumAlonePaysCriticalCeiling = false

round511MissingCoordinateIsInitialCriticalSameObjectRealization : Bool
round511MissingCoordinateIsInitialCriticalSameObjectRealization = true

round511R510InitialCeilingStillOpen : Bool
round511R510InitialCeilingStillOpen =
  R510.round510UniformInitialCriticalCeilingClosed

round511ClayPromotion : Bool
round511ClayPromotion = false

round511Round240CommonInitialDatumOwnedIsTrue :
  round511Round240CommonInitialDatumOwned ≡ true
round511Round240CommonInitialDatumOwnedIsTrue =
  R240.round240CorrectedTrajectoryOwnsCommonInitialDatumIsTrue

round511CommonInitialDatumAlonePaysCriticalCeilingIsFalse :
  round511CommonInitialDatumAlonePaysCriticalCeiling ≡ false
round511CommonInitialDatumAlonePaysCriticalCeilingIsFalse = refl

round511MissingCoordinateIsInitialCriticalSameObjectRealizationIsTrue :
  round511MissingCoordinateIsInitialCriticalSameObjectRealization ≡ true
round511MissingCoordinateIsInitialCriticalSameObjectRealizationIsTrue = refl

round511ClayPromotionIsFalse : round511ClayPromotion ≡ false
round511ClayPromotionIsFalse = refl
