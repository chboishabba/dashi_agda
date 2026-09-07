module DASHI.Physics.Closure.NSTriadKNRetainedViscosityPositivityNoGoRound514Exact where

------------------------------------------------------------------------
-- ROUND514 / SCALAR BARRIER DOES NOT CREATE POSITIVE RETAINED VISCOSITY
--
-- Round104's prose-level physical target explicitly requires strictly positive
-- retained viscosity, while the existing critical-slice/family types carry only
-- the rational coefficients and inequalities.  Hence the algebraic barrier can
-- exist without a typed receipt that
--
--   0 < viscousCoefficient - absorbedCoefficient.
--
-- This is a consumer-visible coordinate: without positive retained viscosity,
-- the dissipation term is not a coercive critical H^(3/2)-type budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Physics.Closure.NSTriadKNUniformGalerkinSignedCriticalProductionRound104Exact as R104

data Empty : Set where

record RetainedViscosityCapabilityModel : Set₁ where
  field
    AlgebraicCriticalBarrierReceipt : Set
    PositiveRetainedViscosityReceipt : Set

open RetainedViscosityCapabilityModel public

barrierWithoutPositiveRetainedViscosity : RetainedViscosityCapabilityModel
barrierWithoutPositiveRetainedViscosity = record
  { AlgebraicCriticalBarrierReceipt = ⊤
  ; PositiveRetainedViscosityReceipt = Empty
  }

BarrierImpliesPositiveRetainedViscosityForEveryModel : Set₁
BarrierImpliesPositiveRetainedViscosityForEveryModel =
  (M : RetainedViscosityCapabilityModel) →
  AlgebraicCriticalBarrierReceipt M →
  PositiveRetainedViscosityReceipt M

algebraicBarrierDoesNotCreatePositiveRetainedViscosity :
  BarrierImpliesPositiveRetainedViscosityForEveryModel → Empty
algebraicBarrierDoesNotCreatePositiveRetainedViscosity promote =
  promote barrierWithoutPositiveRetainedViscosity tt

round514Round104AlgebraicCompilerClosed : Bool
round514Round104AlgebraicCompilerClosed =
  R104.round104SignedProductionToUniformBarrierCompilerClosed

round514PositiveRetainedViscosityTypedInRound104Slice : Bool
round514PositiveRetainedViscosityTypedInRound104Slice = false

round514PositiveRetainedViscosityRequiredByPhysicalTarget : Bool
round514PositiveRetainedViscosityRequiredByPhysicalTarget = true

round514MissingCoordinateIsPositiveRetainedViscosityReceipt : Bool
round514MissingCoordinateIsPositiveRetainedViscosityReceipt = true

round514ClayPromotion : Bool
round514ClayPromotion = false

round514PositiveRetainedViscosityTypedInRound104SliceIsFalse :
  round514PositiveRetainedViscosityTypedInRound104Slice ≡ false
round514PositiveRetainedViscosityTypedInRound104SliceIsFalse = refl

round514PositiveRetainedViscosityRequiredByPhysicalTargetIsTrue :
  round514PositiveRetainedViscosityRequiredByPhysicalTarget ≡ true
round514PositiveRetainedViscosityRequiredByPhysicalTargetIsTrue = refl

round514MissingCoordinateIsPositiveRetainedViscosityReceiptIsTrue :
  round514MissingCoordinateIsPositiveRetainedViscosityReceipt ≡ true
round514MissingCoordinateIsPositiveRetainedViscosityReceiptIsTrue = refl

round514ClayPromotionIsFalse : round514ClayPromotion ≡ false
round514ClayPromotionIsFalse = refl
