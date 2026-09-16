module DASHI.ComputerScience.RSA260BidiGF2BasisCoordinateRowCodecExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiGF2RowCodecMatrixLiftExact as Lift

------------------------------------------------------------------------
-- GF(2)^8 BASIS-COORDINATE ROW CODEC
--
-- The generic matrix-lift owner reduced the structural problem to an exact row
-- codec.  This owner pays the first genuinely algebraic coordinate theorem on
-- the concrete eight-bit GF(2) row carrier: coordinates against the standard
-- basis reconstruct the row definitionally.
--
-- This is intentionally NOT yet the theorem for the runtime's selected
-- low-rank row-space basis.  That implementation chooses a smaller basis and
-- solves coordinates relative to it.  The remaining live debt is therefore
-- the soundness of that selected-basis coordinate solver, not the generic
-- row->matrix plumbing and not the existence of an exact GF(2)^8 coordinate
-- representation.
------------------------------------------------------------------------

record GF2Row8 : Set where
  constructor gf2-row8
  field
    bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 : Bool
open GF2Row8 public

record StandardCoordinates8 : Set where
  constructor standard-coordinates8
  field
    coord0 coord1 coord2 coord3 coord4 coord5 coord6 coord7 : Bool
open StandardCoordinates8 public

encodeStandardCoordinates : GF2Row8 → StandardCoordinates8
encodeStandardCoordinates (gf2-row8 b0 b1 b2 b3 b4 b5 b6 b7) =
  standard-coordinates8 b0 b1 b2 b3 b4 b5 b6 b7

decodeStandardCoordinates : StandardCoordinates8 → GF2Row8
decodeStandardCoordinates (standard-coordinates8 c0 c1 c2 c3 c4 c5 c6 c7) =
  gf2-row8 c0 c1 c2 c3 c4 c5 c6 c7

standardCoordinateRowRoundTrip :
  (row : GF2Row8) →
  decodeStandardCoordinates (encodeStandardCoordinates row) ≡ row
standardCoordinateRowRoundTrip (gf2-row8 b0 b1 b2 b3 b4 b5 b6 b7) = refl

standardBasisRowCodec : Lift.RowCodec GF2Row8 StandardCoordinates8
standardBasisRowCodec =
  Lift.row-codec
    encodeStandardCoordinates
    decodeStandardCoordinates
    standardCoordinateRowRoundTrip

standardBasisMatrixRoundTrip :
  (matrix : Lift.Matrix8 GF2Row8) →
  Lift.decodeMatrix8 standardBasisRowCodec
    (Lift.encodeMatrix8 standardBasisRowCodec matrix)
  ≡ matrix
standardBasisMatrixRoundTrip = Lift.matrix8RoundTrip standardBasisRowCodec

------------------------------------------------------------------------
-- Selected-basis interface.
--
-- The runtime factor codec does not use the full standard basis as its payload;
-- it retains a selected row-space basis plus one coordinate mask per source
-- row.  Once a selected-basis encoder/decoder pays the same row round-trip law,
-- the existing generic matrix theorem applies immediately.  This record makes
-- the remaining obligation explicit instead of treating Python success as the
-- theorem.
------------------------------------------------------------------------

record SelectedBasisCoordinateCodec : Set₁ where
  constructor selected-basis-coordinate-codec
  field
    Coordinates : Set
    encodeSelected : GF2Row8 → Coordinates
    decodeSelected : Coordinates → GF2Row8
    selectedRowRoundTrip :
      (row : GF2Row8) → decodeSelected (encodeSelected row) ≡ row
open SelectedBasisCoordinateCodec public

selectedBasisAsRowCodec :
  (codec : SelectedBasisCoordinateCodec) →
  Lift.RowCodec GF2Row8 (Coordinates codec)
selectedBasisAsRowCodec codec =
  Lift.row-codec
    (encodeSelected codec)
    (decodeSelected codec)
    (selectedRowRoundTrip codec)

selectedBasisMatrixRoundTrip :
  (codec : SelectedBasisCoordinateCodec) →
  (matrix : Lift.Matrix8 GF2Row8) →
  Lift.decodeMatrix8 (selectedBasisAsRowCodec codec)
    (Lift.encodeMatrix8 (selectedBasisAsRowCodec codec) matrix)
  ≡ matrix
selectedBasisMatrixRoundTrip codec =
  Lift.matrix8RoundTrip (selectedBasisAsRowCodec codec)

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record GF2BasisCoordinateRowCodecBoundary : Set where
  constructor gf2-basis-coordinate-row-codec-boundary
  field
    genericRowToMatrixLiftInherited : Bool
    concreteEightBitGF2RowCarrierDefined : Bool
    standardBasisCoordinateEncoderDefined : Bool
    standardBasisCoordinateDecoderDefined : Bool
    standardBasisRowRoundTripProvedExact : Bool
    standardBasisMatrixRoundTripProvedExact : Bool
    selectedBasisCodecInterfaceCompiledToGenericLift : Bool
    selectedLowRankBasisCoordinateSolverSound : Bool
    runtimeBasisSelectionWeldedToFormalSelectedBasis : Bool
    packedEightBitRepresentationProvedExact : Bool
    productionGeneratorCodecCertified : Bool
open GF2BasisCoordinateRowCodecBoundary public

canonicalGF2BasisCoordinateRowCodecBoundary : GF2BasisCoordinateRowCodecBoundary
canonicalGF2BasisCoordinateRowCodecBoundary =
  gf2-basis-coordinate-row-codec-boundary
    true
    true
    true
    true
    true
    true
    true
    false
    false
    false
    false

------------------------------------------------------------------------
-- Roadmap.
--
-- The previous residual "prove a GF(2) basis-coordinate row codec" has now
-- split cleanly.  Full standard-basis coordinates are exact.  The live
-- compression-specific theorem is narrower: prove the selected low-rank
-- row-space coordinate solver sound and weld its basis/mask representation to
-- the runtime factor codec.
------------------------------------------------------------------------

data GF2BasisCoordinateRowCodecResidual : Set where
  proveSelectedLowRankBasisCoordinateSolverSound : GF2BasisCoordinateRowCodecResidual
  weldRuntimeBasisSelectionToFormalSelectedBasis : GF2BasisCoordinateRowCodecResidual
  provePackedEightBitRowRepresentationExact : GF2BasisCoordinateRowCodecResidual
  compileSelectedBasisCodecIntoHybridLayerCodec : GF2BasisCoordinateRowCodecResidual
  compileHybridCodecIntoProductionGeneratorResidualInterface : GF2BasisCoordinateRowCodecResidual
  acquireSameObjectAStarOrFSols : GF2BasisCoordinateRowCodecResidual

firstGF2BasisCoordinateRowCodecResidual : GF2BasisCoordinateRowCodecResidual
firstGF2BasisCoordinateRowCodecResidual =
  proveSelectedLowRankBasisCoordinateSolverSound

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data StandardBasisProofMeansSelectedBasisSolverProof : Set where
data SelectedBasisInterfaceMeansRuntimeBasisWeld : Set where
data ExactRowCoordinatesMeanProductionGeneratorCodec : Set where

standardBasisProofDoesNotCreateSelectedBasisSolverProof :
  StandardBasisProofMeansSelectedBasisSolverProof → ⊥
standardBasisProofDoesNotCreateSelectedBasisSolverProof ()

selectedBasisInterfaceDoesNotCreateRuntimeBasisWeld :
  SelectedBasisInterfaceMeansRuntimeBasisWeld → ⊥
selectedBasisInterfaceDoesNotCreateRuntimeBasisWeld ()

exactRowCoordinatesDoNotCreateProductionCodec :
  ExactRowCoordinatesMeanProductionGeneratorCodec → ⊥
exactRowCoordinatesDoNotCreateProductionCodec ()
