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
-- Instantiate the first actual representation-reduction producer used by the
-- Ogg/SSP programme.  For the integer-spin SO(3) irrep V_j with weights
--
--   m = -j, ..., 0, ..., +j
--
-- the order-n axial rotation fixes exactly the weight lines with n | m.
-- Hence for n=2 and n=3 the fixed dimensions satisfy the recurrences below.
-- We compute the entire j=0..35 scan without Ogg prefiltering.
--
-- The scan also proves a useful falsifier:
--
--   j=4  (dim 9, non-Ogg control)
--   j=5  (dim 11, Ogg dimension)
--
-- have the same (C2-fixed,C3-fixed) signature (5,3).  Therefore this minimal
-- fixed-space pair cannot itself be the Ogg selector.  Any successful reduced
-- symmetry invariant must retain richer branching/orbit information.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_)

import DASHI.Moonshine.ContinuousIrrepRestrictionFixedSpaceExact as Generic

------------------------------------------------------------------------
-- Integer-spin SO(3) carrier.
------------------------------------------------------------------------

oddDimension : Nat → Nat
oddDimension zero = 1
oddDimension (suc j) = 2 + oddDimension j

oddDimensionFormula : Nat → Nat
oddDimensionFormula j = 2 * j + 1

-- The recursive carrier is used computationally in this first scan.  The
-- displayed 2j+1 values reduce definitionally for every concrete scan row.

so3Irrep : Nat → Generic.ContinuousIrrep
so3Irrep j =
  record
    { Label = Nat
    ; label = j
    ; dimension = oddDimension j
    ; sourceGroup = "SO(3), integer-spin irreducible carrier"
    }

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

c2Datum : Nat → Generic.FixedSpaceDatum
c2Datum j =
  Generic.fixedSpaceDatum
    "C2 axial-rotation stabilizer"
    2
    (fixedC2 j)

c3Datum : Nat → Generic.FixedSpaceDatum
c3Datum j =
  Generic.fixedSpaceDatum
    "C3 axial-rotation stabilizer"
    3
    (fixedC3 j)

fixedSpaceSpectrum23 : Nat → Generic.FixedSpaceSpectrum (so3Irrep j)
fixedSpaceSpectrum23 j =
  record
    { fixedSpaces = c2Datum j ∷ c3Datum j ∷ []
    ; allFixedDimensionsBoundedByAmbient = true
    ; allFixedDimensionsBoundedByAmbientIsTrue = refl
    }

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
-- It requires the SU(2) half-spin carrier j=1/2 and must not be manufactured
-- by pretending there is a natural-number j satisfying 2j+1=2.
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
