module DASHI.Astronomy.LocalGroupFirstLightVerificationFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record VerificationFrontier : Set where
  constructor verificationFrontier
  field
    attributionRecorded : Bool
    sourceMetadataRecorded : Bool
    posterClaimsTyped : Bool
    kkh86ResidualRetained : Bool
    exactProducerAcquired : Bool
    independentReproductionRun : Bool
    agdaKernelReceipt : Bool
    frontierNote : String

currentFrontier : VerificationFrontier
currentFrontier =
  verificationFrontier
    true
    true
    true
    true
    false
    false
    false
    "formal source/claim tranche implemented; exact Virtual Observatory producer, independent scientific rerun, and Agda kernel receipt remain unpaid"
