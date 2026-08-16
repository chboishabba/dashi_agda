module DASHI.Moonshine.SO3CyclicFixedSpaceScanExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Add a minimal cyclic-stabilizer producer to the repository's existing
-- FiniteRepresentationRestrictionCore.  For the integer-spin SO(3) irrep V_j
-- with weights
--
--   m = -j, ..., 0, ..., +j,
--
-- an axial rotation of order n fixes exactly the weight lines with n | m.
-- The order-two/order-three dimensions therefore satisfy the recurrences below.
-- We compute j=0..35 without Ogg prefiltering.
--
-- The scan also proves a falsifier:
--
--   j=4  (dim 9, non-Ogg control)
--   j=5  (dim 11, Ogg dimension)
--
-- have the same (C2-fixed,C3-fixed) signature (5,3).  Thus this minimal
-- fixed-space quotient cannot itself explain the Ogg set.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_)

import DASHI.Foundations.FiniteRepresentationRestrictionCore as Generic

------------------------------------------------------------------------
-- Integer-spin SO(3) carrier.
------------------------------------------------------------------------

oddDimension : Nat → Nat
oddDimension zero = 1
oddDimension (suc j) = 2 + oddDimension j

oddDimensionFormula : Nat → Nat
oddDimensionFormula j = 2 * j + 1

so3Irrep : Nat → Generic.ContinuousIrrep
so3Irrep j =
  Generic.continuous-irrep
    j
    (oddDimension j)
    "SO(3) integer-spin irrep"
    "weight carrier m=-j,...,+j; dimension 2j+1"

------------------------------------------------------------------------
-- Exact cyclic fixed-space dimensions by weight divisibility.
------------------------------------------------------------------------

fixedC2 : Nat → Nat
fixedC2 zero = 1
fixedC2 (suc zero) = 1
fixedC2 (suc (suc j)) = 2 + fixedC2 j

fixedC3 : Nat → Nat
fixedC3 zero = 1
fixedC3 (suc zero) = 1
fixedC3 (suc (suc zero)) = 1
fixedC3 (suc (suc (suc j))) = 2 + fixedC3 j

data CyclicFixedProbe : Set where
  c2Probe c3Probe : CyclicFixedProbe

cyclicProbeFixedDimension : Nat → CyclicFixedProbe → Nat
cyclicProbeFixedDimension j c2Probe = fixedC2 j
cyclicProbeFixedDimension j c3Probe = fixedC3 j

cyclicProbeLabel : CyclicFixedProbe → String
cyclicProbeLabel c2Probe = "C2 axial-rotation fixed space"
cyclicProbeLabel c3Probe = "C3 axial-rotation fixed space"

fixedSpaceSpectrum23 : Nat → Generic.FixedSpaceSpectrum
fixedSpaceSpectrum23 j =
  Generic.fixed-space-spectrum
    CyclicFixedProbe
    (cyclicProbeFixedDimension j)
    cyclicProbeLabel
    "SO(3) integer-spin weight divisibility fixed-space spectrum for C2/C3"

------------------------------------------------------------------------
-- Scan rows and an unfiltered j=0..35 producer table.
------------------------------------------------------------------------

record SO3FixedScanRow : Set where
  constructor so3FixedScanRow
  field
    spinJ : Nat
    ambientDimension : Nat
    c2FixedDimension : Nat
    c3FixedDimension : Nat

open SO3FixedScanRow public

scanRow : Nat → SO3FixedScanRow
scanRow j =
  so3FixedScanRow j (oddDimension j) (fixedC2 j) (fixedC3 j)

scanDown : Nat → List SO3FixedScanRow
scanDown zero = scanRow zero ∷ []
scanDown (suc j) = scanRow (suc j) ∷ scanDown j

scan0to35 : List SO3FixedScanRow
scan0to35 = scanDown 35

scanDownLength :
  (j : Nat) →
  length (scanDown j) ≡ suc j
scanDownLength zero = refl
scanDownLength (suc j) rewrite scanDownLength j = refl

scan0to35HasThirtySixRows : length scan0to35 ≡ 36
scan0to35HasThirtySixRows = scanDownLength 35

------------------------------------------------------------------------
-- Exact rows around the first informative Ogg/non-Ogg collision.
------------------------------------------------------------------------

j3DimensionIsSeven : oddDimension 3 ≡ 7
j3DimensionIsSeven = refl

j4DimensionIsNine : oddDimension 4 ≡ 9
j4DimensionIsNine = refl

j5DimensionIsEleven : oddDimension 5 ≡ 11
j5DimensionIsEleven = refl

j6DimensionIsThirteen : oddDimension 6 ≡ 13
j6DimensionIsThirteen = refl

fixedPair : Nat → Nat × Nat
fixedPair j = fixedC2 j , fixedC3 j

j4FixedPair : fixedPair 4 ≡ (5 , 3)
j4FixedPair = refl

j5FixedPair : fixedPair 5 ≡ (5 , 3)
j5FixedPair = refl

j4AndJ5FixedPairsCoincide : fixedPair 4 ≡ fixedPair 5
j4AndJ5FixedPairsCoincide = refl

------------------------------------------------------------------------
-- Further non-Ogg controls requested by the research plan.
------------------------------------------------------------------------

j7DimensionIsFifteen : oddDimension 7 ≡ 15
j7DimensionIsFifteen = refl

j10DimensionIsTwentyOne : oddDimension 10 ≡ 21
j10DimensionIsTwentyOne = refl

j12DimensionIsTwentyFive : oddDimension 12 ≡ 25
j12DimensionIsTwentyFive = refl

j13DimensionIsTwentySeven : oddDimension 13 ≡ 27
j13DimensionIsTwentySeven = refl

j16DimensionIsThirtyThree : oddDimension 16 ≡ 33
j16DimensionIsThirtyThree = refl

------------------------------------------------------------------------
-- The even prime p=2 is deliberately outside the integer-spin SO(3) scan.
------------------------------------------------------------------------

record HalfSpinBoundary : Set where
  constructor halfSpinBoundary
  field
    integerSO3ScanCoversP2 : Bool
    integerSO3ScanCoversP2IsFalse : integerSO3ScanCoversP2 ≡ false
    p2RequiresSeparateSU2HalfSpinLane : Bool
    p2RequiresSeparateSU2HalfSpinLaneIsTrue :
      p2RequiresSeparateSU2HalfSpinLane ≡ true

canonicalHalfSpinBoundary : HalfSpinBoundary
canonicalHalfSpinBoundary = halfSpinBoundary false refl true refl
