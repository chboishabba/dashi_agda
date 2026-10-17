module DASHI.Biology.IITBinaryTernaryParityTorqueLiftExact where

------------------------------------------------------------------------
-- CHARACTERISTIC-2 PARITY -> CHARACTERISTIC-3 SUM / DIFFERENCE SPLIT
--
-- In F2, addition and subtraction coincide, so XOR cannot retain an oriented
-- sign under input reversal.  In the repository's F3-like TriTruth carrier,
-- the same minimal affine idea splits into:
--
--   triSum a b = a + b       (symmetric parity channel)
--   triDiff a b = a - b      (antisymmetric orientation channel)
--
-- and swapping inputs negates triDiff.  This is the exact finite-algebra seam
-- between the IIT parity result and the ordered/Levi-Civita torque geometry in
-- sibling PR #1164.  It does not identify triDiff with physical torque
-- magnitude or manufacture the sibling theorem authority.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Base369 as Base

------------------------------------------------------------------------
-- 1. Binary addition and subtraction collapse to the same XOR table.
------------------------------------------------------------------------

boolXor : Bool → Bool → Bool
boolXor false false = false
boolXor false true = true
boolXor true false = true
boolXor true true = false

boolSub : Bool → Bool → Bool
boolSub false false = false
boolSub false true = true
boolSub true false = true
boolSub true true = false

binaryAdditionEqualsSubtraction :
  (a b : Bool) → boolXor a b ≡ boolSub a b
binaryAdditionEqualsSubtraction false false = refl
binaryAdditionEqualsSubtraction false true = refl
binaryAdditionEqualsSubtraction true false = refl
binaryAdditionEqualsSubtraction true true = refl

binaryParitySwapInvariant :
  (a b : Bool) → boolXor a b ≡ boolXor b a
binaryParitySwapInvariant false false = refl
binaryParitySwapInvariant false true = refl
binaryParitySwapInvariant true false = refl
binaryParitySwapInvariant true true = refl

------------------------------------------------------------------------
-- 2. Exact additive inverse on the existing TriTruth / F3-like carrier.
------------------------------------------------------------------------

triNeg : Base.TriTruth → Base.TriTruth
triNeg Base.tri-low = Base.tri-low
triNeg Base.tri-mid = Base.tri-high
triNeg Base.tri-high = Base.tri-mid

triNegInvolutive : (x : Base.TriTruth) → triNeg (triNeg x) ≡ x
triNegInvolutive Base.tri-low = refl
triNegInvolutive Base.tri-mid = refl
triNegInvolutive Base.tri-high = refl

triSum : Base.TriTruth → Base.TriTruth → Base.TriTruth
triSum = Base.triXor

triDiff : Base.TriTruth → Base.TriTruth → Base.TriTruth
triDiff a b = Base.triXor a (triNeg b)

triSumSwapInvariant :
  (a b : Base.TriTruth) → triSum a b ≡ triSum b a
triSumSwapInvariant Base.tri-low Base.tri-low = refl
triSumSwapInvariant Base.tri-low Base.tri-mid = refl
triSumSwapInvariant Base.tri-low Base.tri-high = refl
triSumSwapInvariant Base.tri-mid Base.tri-low = refl
triSumSwapInvariant Base.tri-mid Base.tri-mid = refl
triSumSwapInvariant Base.tri-mid Base.tri-high = refl
triSumSwapInvariant Base.tri-high Base.tri-low = refl
triSumSwapInvariant Base.tri-high Base.tri-mid = refl
triSumSwapInvariant Base.tri-high Base.tri-high = refl

triDiffSwapNegates :
  (a b : Base.TriTruth) → triDiff b a ≡ triNeg (triDiff a b)
triDiffSwapNegates Base.tri-low Base.tri-low = refl
triDiffSwapNegates Base.tri-low Base.tri-mid = refl
triDiffSwapNegates Base.tri-low Base.tri-high = refl
triDiffSwapNegates Base.tri-mid Base.tri-low = refl
triDiffSwapNegates Base.tri-mid Base.tri-mid = refl
triDiffSwapNegates Base.tri-mid Base.tri-high = refl
triDiffSwapNegates Base.tri-high Base.tri-low = refl
triDiffSwapNegates Base.tri-high Base.tri-mid = refl
triDiffSwapNegates Base.tri-high Base.tri-high = refl

------------------------------------------------------------------------
-- 3. Sum and difference are genuinely distinct in characteristic three.
------------------------------------------------------------------------

ternarySumDifferenceSeparate :
  triSum Base.tri-mid Base.tri-mid ≡ triDiff Base.tri-mid Base.tri-mid → ⊥
ternarySumDifferenceSeparate ()

------------------------------------------------------------------------
-- 4. Authority boundary.
------------------------------------------------------------------------

record BinaryTernaryParityTorqueLiftBoundary : Set where
  constructor binary-ternary-parity-torque-lift-boundary
  field
    binaryAdditionAndSubtractionCollapse : Bool
    binaryParityRetainsSwapHandedness : Bool
    ternarySumIsSymmetric : Bool
    ternaryDifferenceNegatesUnderSwap : Bool
    ternarySumAndDifferenceAreSameLaw : Bool
    antisymmetricDifferenceIsPhysicalTorqueMagnitude : Bool
    siblingTorqueTheoremAuthorityImported : Bool

canonicalBinaryTernaryParityTorqueLiftBoundary :
  BinaryTernaryParityTorqueLiftBoundary
canonicalBinaryTernaryParityTorqueLiftBoundary =
  binary-ternary-parity-torque-lift-boundary
    true false true true false false false
