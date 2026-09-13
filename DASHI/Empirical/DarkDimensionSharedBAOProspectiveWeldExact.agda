module DASHI.Empirical.DarkDimensionSharedBAOProspectiveWeldExact where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Empirical.DarkDimensionDESIDR2BAODataReceiptExact as DR2Data
import DASHI.Empirical.DarkDimensionProspectiveDiscriminatorExact as Prospective
import DASHI.Empirical.DarkDimensionSharedBAOObservableExact as SharedBAO
import DASHI.Empirical.DarkDimensionSharedBAOObservationKeyExact as ObservationKey

------------------------------------------------------------------------
-- THIN SHARED-BAO -> PROSPECTIVE WELD
--
-- The shared observable owner pays that both models meet on the same DESI BAO
-- distance coordinates.  The observation-key owner further requires the same
-- dataset revision / tracer bin / effective redshift / observable identity.
-- The DR2 data owner pays the retrospective observed vector and within-bin
-- correlation coefficients, while retaining that these are not future held-out
-- observations.  The prospective discriminator owns the stronger gate requiring
-- an actual locked numerical separation.  These statuses remain distinct.
------------------------------------------------------------------------

record SharedBAOProspectiveWeldStatus : Set where
  field
    sharedObservableIdentityPaid :
      SharedBAO.sharedObservableIdentityEstablished
        SharedBAO.canonicalSharedBAOStatus
      ≡ true

    sharedObservationKeyIdentityPaid :
      ObservationKey.sharedObservationKeyIdentityEstablished
        ObservationKey.canonicalSharedBAOObservationKeyStatus
      ≡ true

    retrospectiveDR2ValuesRecorded :
      DR2Data.publishedAnisotropicValuesRecorded
        DR2Data.canonicalDESIDR2BAODataStatus
      ≡ true

    retrospectiveDR2StillNotHeldOut :
      DR2Data.futureHeldOutData DR2Data.canonicalDESIDR2BAODataStatus
      ≡ false

    sharedObservableNumericalSeparationOpen :
      SharedBAO.sharedObservableNumericalSeparationLocked
        SharedBAO.canonicalSharedBAOStatus
      ≡ false

    sameKeyNumericalSeparationOpen :
      ObservationKey.sameKeyNumericalSeparationLocked
        ObservationKey.canonicalSharedBAOObservationKeyStatus
      ≡ false

    prospectiveNumericalSeparationOpen :
      Prospective.quantitativeModelSeparationLocked
        Prospective.canonicalProspectiveDiscriminatorPacket
      ≡ false

open SharedBAOProspectiveWeldStatus public

sharedBAOIdentityPaidButNumericalSeparationOpen :
  SharedBAOProspectiveWeldStatus
sharedBAOIdentityPaidButNumericalSeparationOpen = record
  { sharedObservableIdentityPaid = SharedBAO.sharedObservableIdentityPaid
  ; sharedObservationKeyIdentityPaid = ObservationKey.sharedObservationKeyIdentityPaid
  ; retrospectiveDR2ValuesRecorded = refl
  ; retrospectiveDR2StillNotHeldOut =
      DR2Data.retrospectiveDataDoesNotPayHeldOutPrediction
  ; sharedObservableNumericalSeparationOpen =
      SharedBAO.sharedObservableNumericalPredictionsStillOpen
  ; sameKeyNumericalSeparationOpen =
      ObservationKey.sameKeyNumericalModelPredictionsStillOpen
  ; prospectiveNumericalSeparationOpen =
      Prospective.quantitativeEnvelopeStillDoesNotLockProspectivePacket
  }

sameObservationKeyStillRequiredForProspectiveSeparation :
  ObservationKey.sameKeyNumericalSeparationLocked
    ObservationKey.canonicalSharedBAOObservationKeyStatus
  ≡ false
sameObservationKeyStillRequiredForProspectiveSeparation =
  ObservationKey.sameKeyNumericalModelPredictionsStillOpen

retrospectiveDR2DataStillDoesNotLockProspectiveSeparation :
  Prospective.quantitativeModelSeparationLocked
    Prospective.canonicalProspectiveDiscriminatorPacket
  ≡ false
retrospectiveDR2DataStillDoesNotLockProspectiveSeparation =
  Prospective.quantitativeEnvelopeStillDoesNotLockProspectivePacket

sharedBAOStillDoesNotLockProspectivePacket :
  Prospective.quantitativeModelSeparationLocked
    Prospective.canonicalProspectiveDiscriminatorPacket
  ≡ false
sharedBAOStillDoesNotLockProspectivePacket =
  Prospective.quantitativeEnvelopeStillDoesNotLockProspectivePacket
