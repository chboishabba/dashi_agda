module DASHI.Empirical.DarkDimensionSharedBAOProspectiveWeldExact where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Empirical.DarkDimensionProspectiveDiscriminatorExact as Prospective
import DASHI.Empirical.DarkDimensionSharedBAOObservableExact as SharedBAO

------------------------------------------------------------------------
-- THIN SHARED-BAO -> PROSPECTIVE WELD
--
-- The shared observable owner pays that both models meet on the same DESI BAO
-- distance coordinates.  The prospective discriminator owns the stronger gate
-- requiring an actual locked numerical separation.  This adapter keeps those
-- statuses adjacent without merging them.
------------------------------------------------------------------------

record SharedBAOProspectiveWeldStatus : Set where
  field
    sharedObservableIdentityPaid :
      SharedBAO.sharedObservableIdentityEstablished
        SharedBAO.canonicalSharedBAOStatus
      ≡ true

    sharedObservableNumericalSeparationOpen :
      SharedBAO.sharedObservableNumericalSeparationLocked
        SharedBAO.canonicalSharedBAOStatus
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
  ; sharedObservableNumericalSeparationOpen =
      SharedBAO.sharedObservableNumericalPredictionsStillOpen
  ; prospectiveNumericalSeparationOpen =
      Prospective.quantitativeEnvelopeStillDoesNotLockProspectivePacket
  }

sharedBAOStillDoesNotLockProspectivePacket :
  Prospective.quantitativeModelSeparationLocked
    Prospective.canonicalProspectiveDiscriminatorPacket
  ≡ false
sharedBAOStillDoesNotLockProspectivePacket =
  Prospective.quantitativeEnvelopeStillDoesNotLockProspectivePacket
