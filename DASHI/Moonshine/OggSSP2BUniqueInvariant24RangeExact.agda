module DASHI.Moonshine.OggSSP2BUniqueInvariant24RangeExact where

------------------------------------------------------------------------
-- UNIQUE INVARIANT 24-SUBMODULE -> RESIDUAL RANGE IDENTIFICATION
--
-- Stronger preferred Co1 route:
--   * support squeeze forces the actual residual norm image to rank 24;
--   * source-native centralizer equivariance makes that image Co1-stable;
--   * runtime tests whether Sym2(24) has exactly one invariant/minimal
--     24-dimensional submodule and whether it is the explicit Frobenius image.
--
-- If so, literal equality of ranges follows.  This bypasses a separate
-- quotient-source chart M/ker(residual) ~= V24 and its Hom-line identification.
--
-- This owner packages only the proof interface.  The concrete runtime theorem
-- remains external until the GAP screen is executed and ingested.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

record UniqueInvariant24TargetReceipt : Set₁ where
  constructor unique-invariant-24-target-receipt
  field
    TargetSubmodule : Set
    FrobeniusRange : TargetSubmodule
    IsInvariant : TargetSubmodule -> Set
    HasDimension24 : TargetSubmodule -> Set
    frobeniusInvariant : IsInvariant FrobeniusRange
    frobeniusDimension24 : HasDimension24 FrobeniusRange
    uniqueInvariant24 :
      (W : TargetSubmodule) ->
      IsInvariant W ->
      HasDimension24 W ->
      W ≡ FrobeniusRange

open UniqueInvariant24TargetReceipt public

record ActualResidualImageReceipt
    (target : UniqueInvariant24TargetReceipt) : Set₁ where
  constructor actual-residual-image-receipt
  field
    residualRange : TargetSubmodule target
    residualInvariant : IsInvariant target residualRange
    residualDimension24 : HasDimension24 target residualRange

open ActualResidualImageReceipt public

actualResidualRangeIsFrobenius :
  (target : UniqueInvariant24TargetReceipt) ->
  (actual : ActualResidualImageReceipt target) ->
  residualRange actual ≡ FrobeniusRange target
actualResidualRangeIsFrobenius target actual =
  uniqueInvariant24 target
    (residualRange actual)
    (residualInvariant actual)
    (residualDimension24 actual)

record UniqueInvariant24RuntimeBoundary : Set where
  constructor unique-invariant-24-runtime-boundary
  field
    minimalSubmoduleScreenImplemented : Bool
    uniqueMinimal24RuntimePaid : Bool
    uniqueMinimal24EqualsFrobeniusPaid : Bool
    socleEqualsFrobeniusPaid : Bool
    actualResidualRangeInvariantPaid : Bool
    actualResidualRangeDimension24Paid : Bool
    actualResidualRangeIdentifiedWithFrobeniusPaid : Bool

canonicalUniqueInvariant24RuntimeBoundary : UniqueInvariant24RuntimeBoundary
canonicalUniqueInvariant24RuntimeBoundary =
  unique-invariant-24-runtime-boundary
    true false false false
    false true false

-- The generic compiler itself is theorem-paid even though the concrete runtime
-- target theorem remains unexecuted on this branch.
uniqueInvariant24RangeCompilerPaid : Bool
uniqueInvariant24RangeCompilerPaid = true
