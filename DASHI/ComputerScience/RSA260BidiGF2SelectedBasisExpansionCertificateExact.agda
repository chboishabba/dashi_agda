module DASHI.ComputerScience.RSA260BidiGF2SelectedBasisExpansionCertificateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.ComputerScience.RSA260BidiGF2BasisCoordinateRowCodecExact as Basis
import DASHI.ComputerScience.RSA260BidiGF2RowCodecMatrixLiftExact as Lift

------------------------------------------------------------------------
-- PROOF-CARRYING SELECTED-BASIS FACTOR PACKETS
--
-- The runtime hybrid codec chooses a low-rank row-space basis and emits one
-- coordinate mask for each source row.  Proving the Gaussian-elimination / basis
-- selection algorithm itself is one possible route, but it is stronger than the
-- consumer needs.  A smaller trusted boundary is proof-carrying replay:
--
--   basis/mask packet + checked expansion equalities -> exact 8-row matrix.
--
-- This owner formalises that verifier.  The producer may discover coordinates
-- however it likes; the consumer only accepts a packet once every decoded mask
-- is proved equal to its expected row.  No Python execution is imported as a
-- theorem, and no claim is made yet that the existing runtime emits Agda-checkable
-- certificates.
------------------------------------------------------------------------

record SelectedBasisDecoder (Coordinates : Set) : Set where
  constructor selected-basis-decoder
  field
    decodeCoordinates : Coordinates → Basis.GF2Row8
open SelectedBasisDecoder public

record RowExpansionCertificate
  {Coordinates : Set}
  (decoder : SelectedBasisDecoder Coordinates) : Set where
  constructor row-expansion-certificate
  field
    coordinates : Coordinates
    expectedRow : Basis.GF2Row8
    decodedCoordinatesMatch :
      decodeCoordinates decoder coordinates ≡ expectedRow
open RowExpansionCertificate public

record VerifiedMatrixFactorPacket
  {Coordinates : Set}
  (decoder : SelectedBasisDecoder Coordinates) : Set where
  constructor verified-matrix-factor-packet
  field
    row0Certificate : RowExpansionCertificate decoder
    row1Certificate : RowExpansionCertificate decoder
    row2Certificate : RowExpansionCertificate decoder
    row3Certificate : RowExpansionCertificate decoder
    row4Certificate : RowExpansionCertificate decoder
    row5Certificate : RowExpansionCertificate decoder
    row6Certificate : RowExpansionCertificate decoder
    row7Certificate : RowExpansionCertificate decoder
open VerifiedMatrixFactorPacket public

expectedMatrix :
  ∀ {Coordinates : Set}
    {decoder : SelectedBasisDecoder Coordinates} →
  VerifiedMatrixFactorPacket decoder →
  Lift.Matrix8 Basis.GF2Row8
expectedMatrix packet =
  Lift.matrix8
    (expectedRow (row0Certificate packet))
    (expectedRow (row1Certificate packet))
    (expectedRow (row2Certificate packet))
    (expectedRow (row3Certificate packet))
    (expectedRow (row4Certificate packet))
    (expectedRow (row5Certificate packet))
    (expectedRow (row6Certificate packet))
    (expectedRow (row7Certificate packet))

decodeVerifiedPacket :
  ∀ {Coordinates : Set}
    (decoder : SelectedBasisDecoder Coordinates) →
  VerifiedMatrixFactorPacket decoder →
  Lift.Matrix8 Basis.GF2Row8
decodeVerifiedPacket decoder packet =
  Lift.matrix8
    (decodeCoordinates decoder (coordinates (row0Certificate packet)))
    (decodeCoordinates decoder (coordinates (row1Certificate packet)))
    (decodeCoordinates decoder (coordinates (row2Certificate packet)))
    (decodeCoordinates decoder (coordinates (row3Certificate packet)))
    (decodeCoordinates decoder (coordinates (row4Certificate packet)))
    (decodeCoordinates decoder (coordinates (row5Certificate packet)))
    (decodeCoordinates decoder (coordinates (row6Certificate packet)))
    (decodeCoordinates decoder (coordinates (row7Certificate packet)))

verifiedMatrixFactorRoundTrip :
  ∀ {Coordinates : Set}
    (decoder : SelectedBasisDecoder Coordinates)
    (packet : VerifiedMatrixFactorPacket decoder) →
  decodeVerifiedPacket decoder packet ≡ expectedMatrix packet
verifiedMatrixFactorRoundTrip decoder packet
  rewrite decodedCoordinatesMatch (row0Certificate packet)
        | decodedCoordinatesMatch (row1Certificate packet)
        | decodedCoordinatesMatch (row2Certificate packet)
        | decodedCoordinatesMatch (row3Certificate packet)
        | decodedCoordinatesMatch (row4Certificate packet)
        | decodedCoordinatesMatch (row5Certificate packet)
        | decodedCoordinatesMatch (row6Certificate packet)
        | decodedCoordinatesMatch (row7Certificate packet)
  = refl

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record GF2SelectedBasisExpansionCertificateBoundary : Set where
  constructor gf2-selected-basis-expansion-certificate-boundary
  field
    standardCoordinateCodecInherited : Bool
    genericEightRowMatrixLiftInherited : Bool
    selectedBasisDecoderSeparatedFromCoordinateDiscovery : Bool
    oneExpansionEqualityRequiredPerDecodedRow : Bool
    eightCheckedRowEqualitiesReconstructMatrixExactly : Bool
    gaussianEliminationAlgorithmMustBeTrustedByConsumer : Bool
    runtimeCurrentlyEmitsFormalExpansionCertificates : Bool
    runtimeBasisMaskBytesWeldedToFormalCoordinateCarrier : Bool
    packedBitCodecProvedExact : Bool
    productionGeneratorCodecCertified : Bool
open GF2SelectedBasisExpansionCertificateBoundary public

canonicalGF2SelectedBasisExpansionCertificateBoundary :
  GF2SelectedBasisExpansionCertificateBoundary
canonicalGF2SelectedBasisExpansionCertificateBoundary =
  gf2-selected-basis-expansion-certificate-boundary
    true
    true
    true
    true
    true
    false
    false
    false
    false
    false

------------------------------------------------------------------------
-- Pareto consequence.
--
-- We no longer need a universal proof of the producer's coordinate-search
-- algorithm in order to trust replay.  The smaller route is to emit basis/mask
-- expansion certificates, check them, and then reuse the exact matrix lift.
------------------------------------------------------------------------

data GF2SelectedBasisExpansionCertificateResidual : Set where
  emitRuntimeBasisMaskExpansionCertificates : GF2SelectedBasisExpansionCertificateResidual
  weldRuntimeBasisMaskBytesToFormalCoordinates : GF2SelectedBasisExpansionCertificateResidual
  provePackedEightBitRowRepresentationExact : GF2SelectedBasisExpansionCertificateResidual
  compileCertifiedFactorPacketIntoHybridLayerCodec : GF2SelectedBasisExpansionCertificateResidual
  compileHybridCodecIntoProductionGeneratorResidualInterface : GF2SelectedBasisExpansionCertificateResidual
  acquireSameObjectAStarOrFSols : GF2SelectedBasisExpansionCertificateResidual

firstGF2SelectedBasisExpansionCertificateResidual :
  GF2SelectedBasisExpansionCertificateResidual
firstGF2SelectedBasisExpansionCertificateResidual =
  emitRuntimeBasisMaskExpansionCertificates

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data CheckedExpansionMeansProducerSolverProved : Set where
data MatrixReplayCertificateMeansPackedByteProof : Set where
data SyntheticCertificateMeansProductionCustody : Set where

checkedExpansionDoesNotProveProducerSolver :
  CheckedExpansionMeansProducerSolverProved → ⊥
checkedExpansionDoesNotProveProducerSolver ()

matrixReplayCertificateDoesNotCreatePackedByteProof :
  MatrixReplayCertificateMeansPackedByteProof → ⊥
matrixReplayCertificateDoesNotCreatePackedByteProof ()

syntheticCertificateDoesNotCreateProductionCustody :
  SyntheticCertificateMeansProductionCustody → ⊥
syntheticCertificateDoesNotCreateProductionCustody ()
