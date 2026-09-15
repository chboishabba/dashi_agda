module DASHI.ComputerScience.RSA260BidiGF2RowCodecMatrixLiftExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiCoefficientHybridReplayCodecCrossValidationExact as Cross

------------------------------------------------------------------------
-- GENERIC EXACT ROW-CODEC -> 8-ROW MATRIX-CODEC LIFT
--
-- The hybrid runtime factors low-rank 8x8 GF(2) coefficient layers row-wise.
-- The remaining proof debt naturally splits in two:
--
--   (1) generic structural theorem: any exact row codec lifts to an exact
--       eight-row matrix codec;
--   (2) algebraic theorem: the chosen GF(2) basis/coordinate construction is
--       itself an exact row codec.
--
-- This owner pays (1) without pretending to pay (2).  It is polymorphic in the
-- row/code carriers, so it does not smuggle Python, bit packing, or GF(2)
-- semantics into the structural lifting theorem.
------------------------------------------------------------------------

crossValidationBoundary : Cross.HybridCodecCrossValidationBoundary
crossValidationBoundary = Cross.canonicalHybridCodecCrossValidationBoundary

record RowCodec (Row Code : Set) : Set where
  constructor row-codec
  field
    encodeRow : Row → Code
    decodeRow : Code → Row
    rowRoundTrip : (row : Row) → decodeRow (encodeRow row) ≡ row
open RowCodec public

record Matrix8 (Row : Set) : Set where
  constructor matrix8
  field
    row0 row1 row2 row3 row4 row5 row6 row7 : Row
open Matrix8 public

encodeMatrix8 :
  ∀ {Row Code : Set} →
  RowCodec Row Code → Matrix8 Row → Matrix8 Code
encodeMatrix8 codec (matrix8 r0 r1 r2 r3 r4 r5 r6 r7) =
  matrix8
    (encodeRow codec r0)
    (encodeRow codec r1)
    (encodeRow codec r2)
    (encodeRow codec r3)
    (encodeRow codec r4)
    (encodeRow codec r5)
    (encodeRow codec r6)
    (encodeRow codec r7)

decodeMatrix8 :
  ∀ {Row Code : Set} →
  RowCodec Row Code → Matrix8 Code → Matrix8 Row
decodeMatrix8 codec (matrix8 c0 c1 c2 c3 c4 c5 c6 c7) =
  matrix8
    (decodeRow codec c0)
    (decodeRow codec c1)
    (decodeRow codec c2)
    (decodeRow codec c3)
    (decodeRow codec c4)
    (decodeRow codec c5)
    (decodeRow codec c6)
    (decodeRow codec c7)

matrix8RoundTrip :
  ∀ {Row Code : Set}
    (codec : RowCodec Row Code)
    (matrix : Matrix8 Row) →
  decodeMatrix8 codec (encodeMatrix8 codec matrix) ≡ matrix
matrix8RoundTrip codec (matrix8 r0 r1 r2 r3 r4 r5 r6 r7)
  rewrite rowRoundTrip codec r0
        | rowRoundTrip codec r1
        | rowRoundTrip codec r2
        | rowRoundTrip codec r3
        | rowRoundTrip codec r4
        | rowRoundTrip codec r5
        | rowRoundTrip codec r6
        | rowRoundTrip codec r7
  = refl

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record GF2RowCodecMatrixLiftBoundary : Set where
  constructor gf2-row-codec-matrix-lift-boundary
  field
    hybridCodecCrossValidationInherited : Bool
    exactRowCodecLiftsToExactEightRowMatrixCodec : Bool
    theoremIndependentOfGF2Representation : Bool
    theoremIndependentOfPythonRuntime : Bool
    gf2BasisCoordinateEncoderProvedExact : Bool
    bitPackingCodecProvedExact : Bool
    genericVariableDimensionMatrixLiftProved : Bool
    productionGeneratorCodecCertified : Bool
open GF2RowCodecMatrixLiftBoundary public

canonicalGF2RowCodecMatrixLiftBoundary : GF2RowCodecMatrixLiftBoundary
canonicalGF2RowCodecMatrixLiftBoundary =
  gf2-row-codec-matrix-lift-boundary
    true
    true
    true
    true
    false
    false
    false
    false

------------------------------------------------------------------------
-- The live theorem debt is now smaller and genuinely algebraic: instantiate
-- RowCodec for GF(2)^8 using a basis plus coordinate mask and prove the row
-- decoder reconstructs every encoded row.  Only after that do we weld bit
-- packing and the production residual interface.
------------------------------------------------------------------------

data GF2RowCodecMatrixLiftResidual : Set where
  proveGF2BasisCoordinateRowCodecExact : GF2RowCodecMatrixLiftResidual
  provePackedEightBitRowRepresentationExact : GF2RowCodecMatrixLiftResidual
  compileGenericRowCodecIntoHybridLayerCodec : GF2RowCodecMatrixLiftResidual
  compileHybridCodecIntoProductionGeneratorResidualInterface : GF2RowCodecMatrixLiftResidual
  acquireSameObjectAStarOrFSols : GF2RowCodecMatrixLiftResidual

firstGF2RowCodecMatrixLiftResidual : GF2RowCodecMatrixLiftResidual
firstGF2RowCodecMatrixLiftResidual = proveGF2BasisCoordinateRowCodecExact

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data StructuralLiftMeansGF2BasisProof : Set where
data RuntimeCrossValidationMeansGenericTheorem : Set where
data MatrixLiftMeansProductionCodec : Set where

structuralLiftDoesNotCreateGF2BasisProof : StructuralLiftMeansGF2BasisProof → ⊥
structuralLiftDoesNotCreateGF2BasisProof ()

runtimeCrossValidationDoesNotCreateGenericTheorem :
  RuntimeCrossValidationMeansGenericTheorem → ⊥
runtimeCrossValidationDoesNotCreateGenericTheorem ()

matrixLiftDoesNotCreateProductionCodec : MatrixLiftMeansProductionCodec → ⊥
matrixLiftDoesNotCreateProductionCodec ()
