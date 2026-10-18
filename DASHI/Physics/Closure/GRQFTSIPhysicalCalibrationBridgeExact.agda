{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.GRQFTSIPhysicalCalibrationBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.AtomicClockW4ReceiptAdapterRequest as Atomic

data SIPhysicalCalibrationStatus : Set where
  localUnitAndDimensionAdapterPresentExternalAuthorityMissing :
    SIPhysicalCalibrationStatus

record GRQFTSIPhysicalCalibrationBridge : Set where
  constructor grqftSIPhysicalCalibrationBridge
  field
    status : SIPhysicalCalibrationStatus
    candidate256FieldCoveragePresent : Bool
    candidate256FieldCoveragePresentIsTrue :
      candidate256FieldCoveragePresent ≡ true
    exactExternalAuthorityTokenPresent : Bool
    exactExternalAuthorityTokenPresentIsFalse :
      exactExternalAuthorityTokenPresent ≡ false
    candidate256ReceiptConstructed : Bool
    candidate256ReceiptConstructedIsFalse :
      candidate256ReceiptConstructed ≡ false
    localCoverage : List String
    remainingExternalBoundary : List String

open GRQFTSIPhysicalCalibrationBridge public

canonicalGRQFTSIPhysicalCalibrationBridge : GRQFTSIPhysicalCalibrationBridge
canonicalGRQFTSIPhysicalCalibrationBridge =
  grqftSIPhysicalCalibrationBridge
    localUnitAndDimensionAdapterPresentExternalAuthorityMissing
    true refl
    false refl
    false refl
    ( "physicalUnitCarrier"
    ∷ "physicalDimensionVector"
    ∷ "natToUnitCalibrationMap"
    ∷ "calibratedQuotientScaleMap"
    ∷ "scale-map factorization through Candidate256 surrogate"
    ∷ "dimensional-preservation law and witness"
    ∷ [] )
    ( "accepted Candidate256PhysicalCalibrationAuthorityToken"
    ∷ "accepted W4/DY adequacy under the replacement physical shape model"
    ∷ "construction of the exact external Candidate256 receipt after those inputs land"
    ∷ [] )

siCalibrationIsNotWhollyExternal :
  candidate256FieldCoveragePresent canonicalGRQFTSIPhysicalCalibrationBridge ≡ true
siCalibrationIsNotWhollyExternal = refl
