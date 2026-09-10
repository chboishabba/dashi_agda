module DASHI.Astronomy.LocalGroupVerificationStatusExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- The tranche distinguishes formal source integration from kernel checking.
------------------------------------------------------------------------

data VerificationStatus : Set where
  sourceIntegrated : VerificationStatus
  metadataChecked : VerificationStatus
  agdaKernelChecked : VerificationStatus
  independentScienceReproduced : VerificationStatus

sourceIntegratedNow : Bool
sourceIntegratedNow = true

metadataCheckedNow : Bool
metadataCheckedNow = true

agdaKernelCheckedNow : Bool
agdaKernelCheckedNow = false

independentScienceReproducedNow : Bool
independentScienceReproducedNow = false

sourceIntegrationDoesNotImplyKernelCheck : Bool
sourceIntegrationDoesNotImplyKernelCheck = false

sourceIntegrationDoesNotImplyKernelCheckIsFalse :
  sourceIntegrationDoesNotImplyKernelCheck ≡ false
sourceIntegrationDoesNotImplyKernelCheckIsFalse = refl
