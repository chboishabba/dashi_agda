module DASHI.Biology.IITCubePermutationStabilizerRegression where

-- RED-first source contract for the permutation subgroup inside the already
-- characterized diagonal centralizer.

open import DASHI.Core.Prelude
import DASHI.Biology.IITCubeConcreteTorusImageExact as Cube
import DASHI.Biology.IITCubeDiagonalStabilizerExact as Stabilizer

transposePreservesGraphRegression : Stabilizer.PreservesGraph Stabilizer.transposeEndo
transposePreservesGraphRegression = Stabilizer.transposePreservesGraph

transposeIsInvolutionRegression :
  (f : Cube.Face9) → Stabilizer.transposeFace (Stabilizer.transposeFace f) ≡ f
transposeIsInvolutionRegression = Stabilizer.transposeInvolutive

transposeConjugatesRowToColumnRegression :
  (f : Cube.Face9) →
  Stabilizer.transposeFace (Stabilizer.rowShift f)
  ≡ Stabilizer.columnShift (Stabilizer.transposeFace f)
transposeConjugatesRowToColumnRegression = Stabilizer.transposeRowToColumn

transposeConjugatesColumnToRowRegression :
  (f : Cube.Face9) →
  Stabilizer.transposeFace (Stabilizer.columnShift f)
  ≡ Stabilizer.rowShift (Stabilizer.transposeFace f)
transposeConjugatesColumnToRowRegression = Stabilizer.transposeColumnToRow
