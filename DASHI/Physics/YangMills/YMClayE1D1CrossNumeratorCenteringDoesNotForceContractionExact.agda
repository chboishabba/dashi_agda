module DASHI.Physics.YangMills.YMClayE1D1CrossNumeratorCenteringDoesNotForceContractionExact where

------------------------------------------------------------------------
-- A genuinely inhabited FINITE two-point negative control for P0.09.
--
-- This is NOT an SU(N) Wilson source and does not refute an estimate
-- on actual interacting original Wilson Gibbs measures.  It refutes
-- only the logical inference from
--
--       X(1) = 0  and  0 <= F <= 1
--
-- to X(F)=0, or to a small universal RG error independent of a
-- PHYSICAL source estimate.
--
-- Both states below are normalized nonnegative probability measures:
-- the "fine" state is Dirac at right, and the "bare" state is
-- Dirac at left.  All integrals below are genuine finite sums in
-- this two-point model, with Z_fine = Z_bare = 1.
--
-- Hence the cross numerator cancels on unit but is exactly one on
-- the nonconstant indicator.  No external postulates, mock spectral
-- gap, hidden RG contraction or classical excluded-middle principle.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)

data TwoSite : Set where
  left right : TwoSite

one : Nat
one = suc zero

-- Minimal exact natural arithmetic, to avoid assuming any scalar
-- ordered-field or division authority in this negative control.
add : Nat → Nat → Nat
add zero m = m
add (suc n) m = suc (add n m)

multiply : Nat → Nat → Nat
multiply zero m = zero
multiply (suc n) m = add m (multiply n m)

subtract : Nat → Nat → Nat
subtract zero m = zero
subtract (suc n) zero = suc n
subtract (suc n) (suc m) = subtract n m

unit : TwoSite → Nat
unit left = one
unit right = one

indicatorRight : TwoSite → Nat
indicatorRight left = zero
indicatorRight right = one

-- The Dirac measures are genuine two-point finite nonnegative
-- weights; each has exactly one unit of total mass.
fineWeight : TwoSite → Nat
fineWeight left = zero
fineWeight right = one

bareWeight : TwoSite → Nat
bareWeight left = one
bareWeight right = zero

-- Integration is an actual sum over both original points, not
-- a freely postulated linear functional.
finiteWeightedSum : (TwoSite → Nat) → (TwoSite → Nat) → Nat
finiteWeightedSum weight observable =
  add (multiply (weight left) (observable left))
      (multiply (weight right) (observable right))

fineNumerator : (TwoSite → Nat) → Nat
fineNumerator = finiteWeightedSum fineWeight

bareNumerator : (TwoSite → Nat) → Nat
bareNumerator = finiteWeightedSum bareWeight

finePartition : Nat
finePartition = fineNumerator unit

barePartition : Nat
barePartition = bareNumerator unit

sourcePartitionsBothOne :
  (finePartition ≡ one) → (barePartition ≡ one) →
  finePartition ≡ barePartition
sourcePartitionsBothOne refl refl = refl

finePartitionIsOne : finePartition ≡ one
finePartitionIsOne = refl

barePartitionIsOne : barePartition ≡ one
barePartitionIsOne = refl

-- Nat subtraction suffices for the selected nonnegative direction
-- of the witness. This is not offered as signed real cross-numerator
-- semantics for arbitrary observables.
crossNumerator : (TwoSite → Nat) → Nat
crossNumerator observable =
  subtract
    (multiply (fineNumerator observable) barePartition)
    (multiply (bareNumerator observable) finePartition)

unitCrossNumeratorZero : crossNumerator unit ≡ zero
unitCrossNumeratorZero = refl

indicatorBoundedAtLeft : indicatorRight left ≡ zero
indicatorBoundedAtLeft = refl

indicatorBoundedAtRight : indicatorRight right ≡ one
indicatorBoundedAtRight = refl

indicatorFineMomentOne : fineNumerator indicatorRight ≡ one
indicatorFineMomentOne = refl

indicatorBareMomentZero : bareNumerator indicatorRight ≡ zero
indicatorBareMomentZero = refl

-- This nonconstant, certified {0,1}-valued insertion has an
-- ORDER-ONE cross numerator, despite unit cancellation.
indicatorCrossNumeratorOne : crossNumerator indicatorRight ≡ one
indicatorCrossNumeratorOne = refl

-- A parameter-free 0/1-valued "bounded test" does not by itself
-- fix or force the original physical coupling-/scale-dependent
-- error producer for the true SU(N) Wilson RG measures.
