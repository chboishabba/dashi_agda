module DASHI.Environment.SpringfieldPondCertifiedTransportExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Upgrade the existing Springfield pond golden fixture from raw recorded Bool
-- transport checks to the proof-bearing `CertifiedSpatialTransportExact` layer.
-- This gives the LES vertical slice an actual certified directed/capacity path,
-- scale check, timing check and attenuation check.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Environment.CertifiedSpatialTransportExact as Certified
import DASHI.Environment.SpringfieldPondGoldenScenario as Pond

catchmentToDrainCertified :
  Certified.CertifiedTransportEdge Pond.catchmentToDrain
catchmentToDrainCertified =
  Certified.certifiedTransportEdge refl refl
    "fixture flow-direction evidence"
    "fixture uncertainty"

drainToPondCertified :
  Certified.CertifiedTransportEdge Pond.drainToPond
drainToPondCertified =
  Certified.certifiedTransportEdge refl refl
    "fixture inlet evidence"
    "fixture uncertainty"

certifiedPhosphorusPath :
  Certified.CertifiedPath Pond.upperCatchment Pond.pond
certifiedPhosphorusPath =
  Certified.certifiedStep Pond.catchmentToDrain catchmentToDrainCertified
    (Certified.certifiedStep Pond.drainToPond drainToPondCertified
      Certified.certifiedHere)

forgottenCertifiedPathIsGoldenPath :
  Certified.forgetCertifiedPath certifiedPhosphorusPath ≡ Pond.phosphorusPath
forgottenCertifiedPathIsGoldenPath = refl

certifiedSourceSupport :
  Certified.CertifiedSpatialSupport Pond.upperCatchment Pond.pond
certifiedSourceSupport =
  Certified.certifiedSpatialSupport
    Pond.sourceSupport
    certifiedPhosphorusPath
    refl
    refl

certifiedSourceToPond :
  Certified.CertifiedSourceToObservation Pond.upperCatchment Pond.pond
certifiedSourceToPond =
  Certified.certifiedSourceToObservation
    Pond.sourceToPond
    certifiedSourceSupport
    refl
    refl
    refl
