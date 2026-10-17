module DASHI.Biology.IITCubeJordanCentralizerAlgebraExact where

------------------------------------------------------------------------
-- EXACT CENTRALIZER OF THREE EQUAL LENGTH-THREE JORDAN BLOCKS
--
-- The concrete Jordan-basis owner gives an explicit invertible 9x9 basis
-- matrix whose columns are three N=B+I chains.  In those coordinates N acts as
-- three copies of the nilpotent block J with J e2=e1, J e1=e0, J e0=0.
--
-- This module characterizes matrices commuting with that block operator.  Each
-- of the nine 3x3 inter-chain blocks must be
--
--     [ a b c ]
--     [ 0 a b ]
--     [ 0 0 a ]
--
-- i.e. a + b t + c t^2 with t^3=0.  Therefore the Jordan-coordinate
-- centralizer is exactly M3(F3[t]/(t^3)).  This is an algebraic shape theorem;
-- the concrete standard-coordinate transport is supplied by the explicit P/Q
-- basis matrices in IITCubeJordanBasisMatrixExact.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Biology.IITCubeJordanChainCentralizerTargetExact as Target
import DASHI.Biology.IITCubeJordanBasisMatrixExact as Basis

z : Base.TriTruth
z = Base.tri-low

------------------------------------------------------------------------
-- 1. Three chain blocks and three positions in each chain.
------------------------------------------------------------------------

data Block3 : Set where
  blockA blockB blockC : Block3

data Pos3 : Set where
  pos0 pos1 pos2 : Pos3

ix : Block3 → Pos3 → Basis.Ix9
ix blockA pos0 = Basis.i0
ix blockA pos1 = Basis.i1
ix blockA pos2 = Basis.i2
ix blockB pos0 = Basis.i3
ix blockB pos1 = Basis.i4
ix blockB pos2 = Basis.i5
ix blockC pos0 = Basis.i6
ix blockC pos1 = Basis.i7
ix blockC pos2 = Basis.i8

------------------------------------------------------------------------
-- 2. Matrix multiplication by the Jordan operator, written directly in block
--    coordinates so the centralizer equations expose their exact content.
------------------------------------------------------------------------

xTimesJ : Basis.Matrix9 → Block3 → Block3 → Pos3 → Pos3 → Base.TriTruth
xTimesJ matrix rowBlock columnBlock rowPos pos0 = z
xTimesJ matrix rowBlock columnBlock rowPos pos1 =
  matrix (ix rowBlock rowPos) (ix columnBlock pos0)
xTimesJ matrix rowBlock columnBlock rowPos pos2 =
  matrix (ix rowBlock rowPos) (ix columnBlock pos1)

jTimesX : Basis.Matrix9 → Block3 → Block3 → Pos3 → Pos3 → Base.TriTruth
jTimesX matrix rowBlock columnBlock pos0 columnPos =
  matrix (ix rowBlock pos1) (ix columnBlock columnPos)
jTimesX matrix rowBlock columnBlock pos1 columnPos =
  matrix (ix rowBlock pos2) (ix columnBlock columnPos)
jTimesX matrix rowBlock columnBlock pos2 columnPos = z

record CommutesWithThreeJordanBlocks (matrix : Basis.Matrix9) : Set where
  constructor commutes-with-three-jordan-blocks
  field
    commuteEntry :
      (rowBlock columnBlock : Block3) →
      (rowPos columnPos : Pos3) →
      xTimesJ matrix rowBlock columnBlock rowPos columnPos
      ≡ jTimesX matrix rowBlock columnBlock rowPos columnPos
open CommutesWithThreeJordanBlocks public

------------------------------------------------------------------------
-- 3. Equivalent six-equation Toeplitz shape for every inter-chain block.
------------------------------------------------------------------------

record JordanCentralizerShape (matrix : Basis.Matrix9) : Set where
  constructor jordan-centralizer-shape
  field
    below10Zero : (rowBlock columnBlock : Block3) →
      matrix (ix rowBlock pos1) (ix columnBlock pos0) ≡ z
    below20Zero : (rowBlock columnBlock : Block3) →
      matrix (ix rowBlock pos2) (ix columnBlock pos0) ≡ z
    below21Zero : (rowBlock columnBlock : Block3) →
      matrix (ix rowBlock pos2) (ix columnBlock pos1) ≡ z
    diagonal11 : (rowBlock columnBlock : Block3) →
      matrix (ix rowBlock pos0) (ix columnBlock pos0)
      ≡ matrix (ix rowBlock pos1) (ix columnBlock pos1)
    diagonal22 : (rowBlock columnBlock : Block3) →
      matrix (ix rowBlock pos0) (ix columnBlock pos0)
      ≡ matrix (ix rowBlock pos2) (ix columnBlock pos2)
    super12 : (rowBlock columnBlock : Block3) →
      matrix (ix rowBlock pos0) (ix columnBlock pos1)
      ≡ matrix (ix rowBlock pos1) (ix columnBlock pos2)
open JordanCentralizerShape public

shapeImpliesCommutes :
  (matrix : Basis.Matrix9) →
  JordanCentralizerShape matrix →
  CommutesWithThreeJordanBlocks matrix
shapeImpliesCommutes matrix shape =
  commutes-with-three-jordan-blocks commute
  where
  commute :
    (rowBlock columnBlock : Block3) →
    (rowPos columnPos : Pos3) →
    xTimesJ matrix rowBlock columnBlock rowPos columnPos
    ≡ jTimesX matrix rowBlock columnBlock rowPos columnPos
  commute rb cb pos0 pos0 = sym (below10Zero shape rb cb)
  commute rb cb pos0 pos1 = diagonal11 shape rb cb
  commute rb cb pos0 pos2 = super12 shape rb cb
  commute rb cb pos1 pos0 = sym (below20Zero shape rb cb)
  commute rb cb pos1 pos1 =
    trans (below10Zero shape rb cb) (sym (below21Zero shape rb cb))
  commute rb cb pos1 pos2 =
    trans (sym (diagonal11 shape rb cb)) (diagonal22 shape rb cb)
  commute rb cb pos2 pos0 = refl
  commute rb cb pos2 pos1 = below20Zero shape rb cb
  commute rb cb pos2 pos2 = below21Zero shape rb cb

commutesImpliesShape :
  (matrix : Basis.Matrix9) →
  CommutesWithThreeJordanBlocks matrix →
  JordanCentralizerShape matrix
commutesImpliesShape matrix commutes =
  jordan-centralizer-shape
    (λ rb cb → sym (commuteEntry commutes rb cb pos0 pos0))
    (λ rb cb → sym (commuteEntry commutes rb cb pos1 pos0))
    (λ rb cb → commuteEntry commutes rb cb pos2 pos2)
    (λ rb cb → commuteEntry commutes rb cb pos0 pos1)
    (λ rb cb →
      trans
        (commuteEntry commutes rb cb pos0 pos1)
        (commuteEntry commutes rb cb pos1 pos2))
    (λ rb cb → commuteEntry commutes rb cb pos0 pos2)

record JordanCommutationShapeEquivalence (matrix : Basis.Matrix9) : Set where
  constructor jordan-commutation-shape-equivalence
  field
    commutationToShape : CommutesWithThreeJordanBlocks matrix → JordanCentralizerShape matrix
    shapeToCommutation : JordanCentralizerShape matrix → CommutesWithThreeJordanBlocks matrix
open JordanCommutationShapeEquivalence public

jordanCommutationIffToeplitzShape :
  (matrix : Basis.Matrix9) → JordanCommutationShapeEquivalence matrix
jordanCommutationIffToeplitzShape matrix =
  jordan-commutation-shape-equivalence
    (commutesImpliesShape matrix)
    (shapeImpliesCommutes matrix)

------------------------------------------------------------------------
-- 4. Convert a 3x3 matrix of truncated polynomials to the 9x9 Toeplitz blocks.
------------------------------------------------------------------------

polyAt : Target.Matrix3Poly → Block3 → Block3 → Target.TruncatedPoly3
polyAt matrix blockA blockA = Target.p00 matrix
polyAt matrix blockA blockB = Target.p01 matrix
polyAt matrix blockA blockC = Target.p02 matrix
polyAt matrix blockB blockA = Target.p10 matrix
polyAt matrix blockB blockB = Target.p11 matrix
polyAt matrix blockB blockC = Target.p12 matrix
polyAt matrix blockC blockA = Target.p20 matrix
polyAt matrix blockC blockB = Target.p21 matrix
polyAt matrix blockC blockC = Target.p22 matrix

toeplitzEntry : Target.TruncatedPoly3 → Pos3 → Pos3 → Base.TriTruth
toeplitzEntry poly pos0 pos0 = Target.c0 poly
toeplitzEntry poly pos0 pos1 = Target.c1 poly
toeplitzEntry poly pos0 pos2 = Target.c2 poly
toeplitzEntry poly pos1 pos0 = z
toeplitzEntry poly pos1 pos1 = Target.c0 poly
toeplitzEntry poly pos1 pos2 = Target.c1 poly
toeplitzEntry poly pos2 pos0 = z
toeplitzEntry poly pos2 pos1 = z
toeplitzEntry poly pos2 pos2 = Target.c0 poly

blockOfIx : Basis.Ix9 → Block3
blockOfIx Basis.i0 = blockA
blockOfIx Basis.i1 = blockA
blockOfIx Basis.i2 = blockA
blockOfIx Basis.i3 = blockB
blockOfIx Basis.i4 = blockB
blockOfIx Basis.i5 = blockB
blockOfIx Basis.i6 = blockC
blockOfIx Basis.i7 = blockC
blockOfIx Basis.i8 = blockC

posOfIx : Basis.Ix9 → Pos3
posOfIx Basis.i0 = pos0
posOfIx Basis.i1 = pos1
posOfIx Basis.i2 = pos2
posOfIx Basis.i3 = pos0
posOfIx Basis.i4 = pos1
posOfIx Basis.i5 = pos2
posOfIx Basis.i6 = pos0
posOfIx Basis.i7 = pos1
posOfIx Basis.i8 = pos2

expandCentralizer : Target.Matrix3Poly → Basis.Matrix9
expandCentralizer matrix row column =
  toeplitzEntry
    (polyAt matrix (blockOfIx row) (blockOfIx column))
    (posOfIx row)
    (posOfIx column)

expandCentralizerShape :
  (matrix : Target.Matrix3Poly) →
  JordanCentralizerShape (expandCentralizer matrix)
expandCentralizerShape matrix =
  jordan-centralizer-shape
    (λ rb cb → refl)
    (λ rb cb → refl)
    (λ rb cb → refl)
    (λ rb cb → refl)
    (λ rb cb → refl)
    (λ rb cb → refl)

expandCentralizerCommutes :
  (matrix : Target.Matrix3Poly) →
  CommutesWithThreeJordanBlocks (expandCentralizer matrix)
expandCentralizerCommutes matrix =
  shapeImpliesCommutes (expandCentralizer matrix) (expandCentralizerShape matrix)

------------------------------------------------------------------------
-- 5. Extract the three polynomial coefficients from each Toeplitz block.
------------------------------------------------------------------------

extractPoly : Basis.Matrix9 → Block3 → Block3 → Target.TruncatedPoly3
extractPoly matrix rowBlock columnBlock = Target.poly3
  (matrix (ix rowBlock pos0) (ix columnBlock pos0))
  (matrix (ix rowBlock pos0) (ix columnBlock pos1))
  (matrix (ix rowBlock pos0) (ix columnBlock pos2))

extractCentralizer : Basis.Matrix9 → Target.Matrix3Poly
extractCentralizer matrix = Target.matrix3poly
  (extractPoly matrix blockA blockA)
  (extractPoly matrix blockA blockB)
  (extractPoly matrix blockA blockC)
  (extractPoly matrix blockB blockA)
  (extractPoly matrix blockB blockB)
  (extractPoly matrix blockB blockC)
  (extractPoly matrix blockC blockA)
  (extractPoly matrix blockC blockB)
  (extractPoly matrix blockC blockC)

extractExpand :
  (matrix : Target.Matrix3Poly) →
  extractCentralizer (expandCentralizer matrix) ≡ matrix
extractExpand (Target.matrix3poly
  (Target.poly3 a00 a01 a02)
  (Target.poly3 b00 b01 b02)
  (Target.poly3 c00 c01 c02)
  (Target.poly3 d00 d01 d02)
  (Target.poly3 e00 e01 e02)
  (Target.poly3 f00 f01 f02)
  (Target.poly3 g00 g01 g02)
  (Target.poly3 h00 h01 h02)
  (Target.poly3 i00 i01 i02)) = refl

expandExtractPointwise :
  (matrix : Basis.Matrix9) →
  JordanCentralizerShape matrix →
  (rowBlock columnBlock : Block3) →
  (rowPos columnPos : Pos3) →
  expandCentralizer (extractCentralizer matrix)
    (ix rowBlock rowPos) (ix columnBlock columnPos)
  ≡ matrix (ix rowBlock rowPos) (ix columnBlock columnPos)
expandExtractPointwise matrix shape rb cb pos0 pos0 = refl
expandExtractPointwise matrix shape rb cb pos0 pos1 = refl
expandExtractPointwise matrix shape rb cb pos0 pos2 = refl
expandExtractPointwise matrix shape rb cb pos1 pos0 = sym (below10Zero shape rb cb)
expandExtractPointwise matrix shape rb cb pos1 pos1 = diagonal11 shape rb cb
expandExtractPointwise matrix shape rb cb pos1 pos2 = super12 shape rb cb
expandExtractPointwise matrix shape rb cb pos2 pos0 = sym (below20Zero shape rb cb)
expandExtractPointwise matrix shape rb cb pos2 pos1 = sym (below21Zero shape rb cb)
expandExtractPointwise matrix shape rb cb pos2 pos2 = diagonal22 shape rb cb

record JordanCentralizerPolynomialEquivalence : Set₁ where
  constructor jordan-centralizer-polynomial-equivalence
  field
    toPolynomialMatrix : Basis.Matrix9 → Target.Matrix3Poly
    fromPolynomialMatrix : Target.Matrix3Poly → Basis.Matrix9
    everyPolynomialMatrixCommutes :
      (matrix : Target.Matrix3Poly) →
      CommutesWithThreeJordanBlocks (fromPolynomialMatrix matrix)
    polynomialRoundTrip :
      (matrix : Target.Matrix3Poly) →
      toPolynomialMatrix (fromPolynomialMatrix matrix) ≡ matrix
    commutingMatrixRoundTripPointwise :
      (matrix : Basis.Matrix9) →
      CommutesWithThreeJordanBlocks matrix →
      (rowBlock columnBlock : Block3) →
      (rowPos columnPos : Pos3) →
      fromPolynomialMatrix (toPolynomialMatrix matrix)
        (ix rowBlock rowPos) (ix columnBlock columnPos)
      ≡ matrix (ix rowBlock rowPos) (ix columnBlock columnPos)
open JordanCentralizerPolynomialEquivalence public

canonicalJordanCentralizerPolynomialEquivalence :
  JordanCentralizerPolynomialEquivalence
canonicalJordanCentralizerPolynomialEquivalence =
  jordan-centralizer-polynomial-equivalence
    extractCentralizer
    expandCentralizer
    expandCentralizerCommutes
    extractExpand
    (λ matrix commutes →
      expandExtractPointwise matrix (commutesImpliesShape matrix commutes))

record JordanCentralizerAlgebraBoundary : Set where
  constructor jordan-centralizer-algebra-boundary
  field
    threeJordanBlocksHaveToeplitzCentralizerShape : Bool
    polynomialMatrixExpansionCommutes : Bool
    everyCommutingMatrixExtractsToPolynomialMatrix : Bool
    extractionExpansionRoundTrips : Bool
    targetRingHasT3Zero : Bool
    standardCoordinateTransportUsesExplicitPQBasis : Bool
    physicalExceptionalSymmetryIdentifiedAutomatically : Bool
open JordanCentralizerAlgebraBoundary public

canonicalJordanCentralizerAlgebraBoundary : JordanCentralizerAlgebraBoundary
canonicalJordanCentralizerAlgebraBoundary =
  jordan-centralizer-algebra-boundary true true true true true true false
