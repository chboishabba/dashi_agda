module DASHI.ComputerScience.RSA260BidiGF2BasisCoordinateRowCodecValidationExact where

import DASHI.ComputerScience.RSA260BidiGF2BasisCoordinateRowCodecExact as Codec
import DASHI.ComputerScience.RSA260BidiGF2RowCodecMatrixLiftExact as Lift

rowRoundTrip :
  (row : Codec.GF2Row8) →
  Codec.decodeStandardCoordinates (Codec.encodeStandardCoordinates row) ≡ row
rowRoundTrip = Codec.standardCoordinateRowRoundTrip

rowCodec : Lift.RowCodec Codec.GF2Row8 Codec.StandardCoordinates8
rowCodec = Codec.standardBasisRowCodec

matrixRoundTrip :
  (matrix : Lift.Matrix8 Codec.GF2Row8) →
  Lift.decodeMatrix8 rowCodec (Lift.encodeMatrix8 rowCodec matrix) ≡ matrix
matrixRoundTrip = Codec.standardBasisMatrixRoundTrip

boundary : Codec.GF2BasisCoordinateRowCodecBoundary
boundary = Codec.canonicalGF2BasisCoordinateRowCodecBoundary

firstResidual : Codec.GF2BasisCoordinateRowCodecResidual
firstResidual = Codec.firstGF2BasisCoordinateRowCodecResidual
