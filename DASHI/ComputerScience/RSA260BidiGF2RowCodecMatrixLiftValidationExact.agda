module DASHI.ComputerScience.RSA260BidiGF2RowCodecMatrixLiftValidationExact where

import DASHI.ComputerScience.RSA260BidiGF2RowCodecMatrixLiftExact as Lift

roundTrip :
  ∀ {Row Code : Set}
    (codec : Lift.RowCodec Row Code)
    (matrix : Lift.Matrix8 Row) →
  Lift.decodeMatrix8 codec (Lift.encodeMatrix8 codec matrix) ≡ matrix
roundTrip = Lift.matrix8RoundTrip

boundary : Lift.GF2RowCodecMatrixLiftBoundary
boundary = Lift.canonicalGF2RowCodecMatrixLiftBoundary

firstResidual : Lift.GF2RowCodecMatrixLiftResidual
firstResidual = Lift.firstGF2RowCodecMatrixLiftResidual
