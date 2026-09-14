module DASHI.Physics.WaveProjectionLossAdapterExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.ShiftWaveRefinementSeam as Wave

------------------------------------------------------------------------
-- WAVE REFINEMENT STATUS AGAINST GENERIC PROJECTION LOSS
--
-- The current seam proves exact finite project/embed and transport relations.
-- It does not currently expose two fine observations with the same coarse
-- projection that a consumer separates.  Therefore no static collision theorem
-- is promoted here.
------------------------------------------------------------------------

record WaveProjectionStatus : Set where
  constructor waveProjectionStatusRecord
  field
    finiteProjectionAgreementLocated : Bool
    finiteTransportCompatibilityLocated : Bool
    staticProjectionCollisionLocated : Bool
    staticNonrecoverabilityPromoted : Bool
    dynamicNoncongruenceInferredFromStaticLoss : Bool

waveProjectionStatus : WaveProjectionStatus
waveProjectionStatus =
  waveProjectionStatusRecord true true false false false

finiteProjectionAgreementLocatedIsTrue :
  WaveProjectionStatus.finiteProjectionAgreementLocated waveProjectionStatus
    ≡ true
finiteProjectionAgreementLocatedIsTrue = refl

staticProjectionCollisionStillUnpaid :
  WaveProjectionStatus.staticProjectionCollisionLocated waveProjectionStatus
    ≡ false
staticProjectionCollisionStillUnpaid = refl

existingProjectAgreement : Wave.projectFineAgreement
existingProjectAgreement = Wave.projectFineAgreement-witness

existingCoarseTransport : Wave.coarseTransportCompatibility
existingCoarseTransport = Wave.coarseTransportCompatibility-witness
