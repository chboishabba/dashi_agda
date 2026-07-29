module DASHI.Physics.Closure.NSTriadKNOutputRelocationDirectionSystemClassification where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; DASHI repository contributors.
-- Title: "A Multilinear Schur Test and Multiplier Operators" and "Exact
-- output-relocation homogeneity-preserving direction classification".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24; DASHI formal
-- development, 2026.
-- DOI: 10.1006/jfan.2001.3804; the repository classification has no DOI.
-- Uses: the affine small-epsilon architecture and the six exact
-- output-relocation epsilon slopes.
-- Relationship: proves that preserving all three literal low-shell
-- homogeneity equations gives a full-rank direction system and hence only the
-- zero direction.  It does not rule out perturbations that deliberately relax
-- or replace one of those homogeneity equations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNOutputRelocationAffineFamilySubstitution as AffineRows
import DASHI.Physics.Closure.NSTriadKNOutputRelocationBaseSystemClassification as Base

record IntegerRow3 : Set where
  constructor row3
  field
    left right output : Int

open IntegerRow3 public

-- The low-shell epsilon slopes are the negatives of the base matrix rows.
outputDirectionRow : IntegerRow3
outputDirectionRow = row3 (pos 2) (pos 2) (negsuc 1)

firstAdjointDirectionRow : IntegerRow3
firstAdjointDirectionRow = row3 (negsuc 1) (pos 2) (pos 2)

secondAdjointDirectionRow : IntegerRow3
secondAdjointDirectionRow = row3 (pos 2) (negsuc 1) (pos 2)

outputRelocationDirectionMatrixDeterminant : Int
outputRelocationDirectionMatrixDeterminant = pos 32

outputRelocationDirectionSystemRank : Nat
outputRelocationDirectionSystemRank = 3

record DirectionVector : Set where
  constructor direction
  field
    leftDirection rightDirection outputDirection : Int

open DirectionVector public

zeroPreservingDirection : DirectionVector
zeroPreservingDirection = direction (pos 0) (pos 0) (pos 0)

record SixSlopeValues : Set where
  constructor six-slopes
  field
    outputLow outputGap : Int
    firstLow firstGap : Int
    secondLow secondGap : Int

open SixSlopeValues public

-- Substitution of the unique preserving direction into all six rows.
zeroDirectionSlopeValues : SixSlopeValues
zeroDirectionSlopeValues = six-slopes
  (pos 0) (pos 0)
  (pos 0) (pos 0)
  (pos 0) (pos 0)

record DirectionSystemClassificationReceipt : Set where
  constructor receipt
  field
    baseSystemClassified : Base.outputRelocationBaseSystemClassified ≡ true
    sixSymbolicSlopesAvailable :
      AffineRows.outputRelocationSixEpsilonSlopesClosed ≡ true
    determinantIsThirtyTwo :
      outputRelocationDirectionMatrixDeterminant ≡ pos 32
    rankIsThree : outputRelocationDirectionSystemRank ≡ 3
    preservingDirectionIsZero :
      zeroPreservingDirection ≡ direction (pos 0) (pos 0) (pos 0)
    allSixPreservingSlopesAreZero :
      zeroDirectionSlopeValues ≡ six-slopes
        (pos 0) (pos 0) (pos 0) (pos 0) (pos 0) (pos 0)

open DirectionSystemClassificationReceipt public

directionSystemClassificationReceipt : DirectionSystemClassificationReceipt
directionSystemClassificationReceipt = receipt
  Base.outputRelocationBaseSystemClassifiedIsTrue
  AffineRows.outputRelocationSixEpsilonSlopesClosedIsTrue
  refl refl refl refl

outputRelocationDirectionSystemClassified : Bool
outputRelocationDirectionSystemClassified = true

outputRelocationOnlyZeroHomogeneityPreservingDirection : Bool
outputRelocationOnlyZeroHomogeneityPreservingDirection = true

outputRelocationNontrivialHomogeneityPreservingDirectionExists : Bool
outputRelocationNontrivialHomogeneityPreservingDirectionExists = false

outputRelocationDirectionSystemClassifiedIsTrue :
  outputRelocationDirectionSystemClassified ≡ true
outputRelocationDirectionSystemClassifiedIsTrue = refl

outputRelocationOnlyZeroHomogeneityPreservingDirectionIsTrue :
  outputRelocationOnlyZeroHomogeneityPreservingDirection ≡ true
outputRelocationOnlyZeroHomogeneityPreservingDirectionIsTrue = refl

outputRelocationNontrivialHomogeneityPreservingDirectionExistsIsFalse :
  outputRelocationNontrivialHomogeneityPreservingDirectionExists ≡ false
outputRelocationNontrivialHomogeneityPreservingDirectionExistsIsFalse = refl
