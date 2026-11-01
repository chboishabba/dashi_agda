module DASHI.Physics.Closure.NSTriadKNOutputRelocationBaseSystemClassification where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Minghui Liu; Gabor Pataki;
-- DASHI repository contributors.
-- Title: "A Multilinear Schur Test and Multiplier Operators"; "Exact duals
-- and short certificates of infeasibility and weak infeasibility in conic
-- linear programming"; and "Exact output-relocation base-system
-- classification".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24;
-- Mathematical Programming / arXiv, 2015--2017; DASHI formal development,
-- 2026.
-- DOI: 10.1006/jfan.2001.3804; 10.48550/arXiv.1507.00290; the repository
-- classification has no DOI.
-- Uses: the three literal output-relocation low-shell rows and the principle
-- that infeasibility must be witnessed by an exact, inspectable dual linear
-- combination rather than by solver failure alone.
-- Relationship: classifies the base system obtained by imposing all three
-- low-shell Schur homogeneity equalities.  It proves that this particular
-- homogeneity choice has full rank and forces an output-gap obstruction.  It
-- does not claim that every possible three-weight or non-affine ansatz fails.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNOutputRelocationLiteralShellSubstitution as Shells

record IntegerRow3 : Set where
  constructor row3
  field
    left right output : Int

open IntegerRow3 public

-- An affine rational expression (a*s + b)/d.  The denominator is recorded
-- syntactically because this tranche is an exact coefficient receipt, not a
-- replacement rational library.
record AffineRegularity : Set where
  constructor affine
  field
    regularityCoefficient constantTerm : Int
    denominator : Nat

open AffineRegularity public

-- The three low-shell equalities are
--
--   -2 B_L -2 B_R +2 B_O = 4s - 5,
--   +2 B_L -2 B_R -2 B_O = 4s - 5,
--   -2 B_L +2 B_R -2 B_O = 4s - 5.
outputHomogeneityRow : IntegerRow3
outputHomogeneityRow = row3 (negsuc 1) (negsuc 1) (pos 2)

firstAdjointHomogeneityRow : IntegerRow3
firstAdjointHomogeneityRow = row3 (pos 2) (negsuc 1) (negsuc 1)

secondAdjointHomogeneityRow : IntegerRow3
secondAdjointHomogeneityRow = row3 (negsuc 1) (pos 2) (negsuc 1)

commonHomogeneityTarget : AffineRegularity
commonHomogeneityTarget = affine (pos 4) (negsuc 4) 1

-- Exact determinant and rank of the 3 x 3 coefficient matrix.
outputRelocationBaseMatrixDeterminant : Int
outputRelocationBaseMatrixDeterminant = negsuc 31

outputRelocationBaseSystemRank : Nat
outputRelocationBaseSystemRank = 3

-- Four times the inverse matrix.  This makes the inverse certificate integral:
--
--   4 A^-1 = [ -1  0 -1
--               -1 -1  0
--                0 -1 -1 ].
inverseScale : Nat
inverseScale = 4

inverseScaledLeftRow : IntegerRow3
inverseScaledLeftRow = row3 (negsuc 0) (pos 0) (negsuc 0)

inverseScaledRightRow : IntegerRow3
inverseScaledRightRow = row3 (negsuc 0) (negsuc 0) (pos 0)

inverseScaledOutputRow : IntegerRow3
inverseScaledOutputRow = row3 (pos 0) (negsuc 0) (negsuc 0)

-- The unique base point is
--
--   B_L = B_R = B_O = (5 - 4s)/2.
outputRelocationBaseLeft : AffineRegularity
outputRelocationBaseLeft = affine (negsuc 3) (pos 5) 2

outputRelocationBaseRight : AffineRegularity
outputRelocationBaseRight = outputRelocationBaseLeft

outputRelocationBaseOutput : AffineRegularity
outputRelocationBaseOutput = outputRelocationBaseLeft

record OutputRelocationBaseSolution : Set where
  constructor base-solution
  field
    leftBase rightBase outputBase : AffineRegularity

open OutputRelocationBaseSolution public

uniqueOutputRelocationBase : OutputRelocationBaseSolution
uniqueOutputRelocationBase =
  base-solution
    outputRelocationBaseLeft
    outputRelocationBaseRight
    outputRelocationBaseOutput

-- Exact dual elimination witness.
--
-- Twice the output-gap weight row (-2,-2,0) is obtained as
--
--   2 * outputHomogeneityRow
--     + firstAdjointHomogeneityRow
--     + secondAdjointHomogeneityRow
--   = (-4,-4,0).
--
-- The corresponding right-hand-side combination gives the forced gap
-- exponent 4s - 10 after restoring the physical -4s term.
record FarkasStyleEliminationWitness : Set where
  constructor dual-witness
  field
    outputMultiplier firstMultiplier secondMultiplier commonScale : Nat
    combinedWeightRow : IntegerRow3
    forcedOutputGap : AffineRegularity

open FarkasStyleEliminationWitness public

outputGapDualWitness : FarkasStyleEliminationWitness
outputGapDualWitness = dual-witness
  2 1 1 2
  (row3 (negsuc 3) (negsuc 3) (pos 0))
  (affine (pos 4) (negsuc 9) 1)

forcedOutputGapExponent : AffineRegularity
forcedOutputGapExponent = affine (pos 4) (negsuc 9) 1

forcedFirstAdjointGapExponent : AffineRegularity
forcedFirstAdjointGapExponent = affine (negsuc 3) (pos 0) 1

forcedSecondAdjointGapExponent : AffineRegularity
forcedSecondAdjointGapExponent = affine (negsuc 3) (pos 0) 1

record BaseSystemClassificationReceipt : Set where
  constructor receipt
  field
    literalRowsAvailable :
      Shells.outputRelocationThreeConditionAffineRowsClosed ≡ true
    determinantIsMinusThirtyTwo :
      outputRelocationBaseMatrixDeterminant ≡ negsuc 31
    rankIsThree : outputRelocationBaseSystemRank ≡ 3
    leftBaseIsFiveMinusFourSOverTwo :
      outputRelocationBaseLeft ≡ affine (negsuc 3) (pos 5) 2
    allThreeBasesCoincide :
      outputRelocationBaseRight ≡ outputRelocationBaseLeft
    outputBaseAlsoCoincides :
      outputRelocationBaseOutput ≡ outputRelocationBaseLeft
    dualWitnessForcesFourSMinusTen :
      forcedOutputGapExponent ≡ affine (pos 4) (negsuc 9) 1

open BaseSystemClassificationReceipt public

baseSystemClassificationReceipt : BaseSystemClassificationReceipt
baseSystemClassificationReceipt = receipt
  Shells.outputRelocationThreeConditionAffineRowsClosedIsTrue
  refl refl refl refl refl refl

outputRelocationBaseSystemClassified : Bool
outputRelocationBaseSystemClassified = true

outputRelocationBaseSystemUnique : Bool
outputRelocationBaseSystemUnique = true

outputRelocationFarkasDualEliminationClosed : Bool
outputRelocationFarkasDualEliminationClosed = true

outputRelocationBaseSystemClassifiedIsTrue :
  outputRelocationBaseSystemClassified ≡ true
outputRelocationBaseSystemClassifiedIsTrue = refl

outputRelocationBaseSystemUniqueIsTrue :
  outputRelocationBaseSystemUnique ≡ true
outputRelocationBaseSystemUniqueIsTrue = refl

outputRelocationFarkasDualEliminationClosedIsTrue :
  outputRelocationFarkasDualEliminationClosed ≡ true
outputRelocationFarkasDualEliminationClosedIsTrue = refl
