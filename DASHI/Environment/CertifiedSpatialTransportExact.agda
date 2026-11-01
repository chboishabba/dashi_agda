module DASHI.Environment.CertifiedSpatialTransportExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- `SpatialTransport` intentionally records raw runtime facts, including Bool
-- checks.  A raw `Path` therefore proves topological chaining of recorded edges,
-- not that direction/capacity/scale/timing/attenuation checks succeeded.
-- This module adds the proof-bearing promotion layer required for claims such as
-- source attribution or capacity-certified transport.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

import DASHI.Environment.SpatialTransport as Spatial

record CertifiedTransportEdge
    {from to : Spatial.SpatialNode}
    (edge : Spatial.TransportEdge from to) : Set where
  constructor certifiedTransportEdge
  field
    directionCertified : Spatial.directionVerified edge ≡ true
    capacityOrConductanceCertified :
      Spatial.capacityOrConductanceRecorded edge ≡ true
    evidenceWitness : String
    uncertaintyWitness : String

open CertifiedTransportEdge public

data CertifiedPath : Spatial.SpatialNode → Spatial.SpatialNode → Set where
  certifiedHere : ∀ {x} → CertifiedPath x x
  certifiedStep :
    ∀ {x y z} →
    (edge : Spatial.TransportEdge x y) →
    CertifiedTransportEdge edge →
    CertifiedPath y z →
    CertifiedPath x z

forgetCertifiedPath :
  ∀ {x y} → CertifiedPath x y → Spatial.Path x y
forgetCertifiedPath certifiedHere = Spatial.here
forgetCertifiedPath (certifiedStep edge certificate rest) =
  Spatial.step edge (forgetCertifiedPath rest)

certifiedPathAppend :
  ∀ {x y z} →
  CertifiedPath x y →
  CertifiedPath y z →
  CertifiedPath x z
certifiedPathAppend certifiedHere right = right
certifiedPathAppend (certifiedStep edge certificate rest) right =
  certifiedStep edge certificate (certifiedPathAppend rest right)

record CertifiedSpatialSupport
    (source target : Spatial.SpatialNode) : Set where
  constructor certifiedSpatialSupport
  field
    rawSupport : Spatial.SpatialSupport source target
    transportPath : CertifiedPath source target
    pathMatchesRaw :
      forgetCertifiedPath transportPath ≡ Spatial.physicalPath rawSupport
    scaleCheck : Spatial.scaleCompatible rawSupport ≡ true

open CertifiedSpatialSupport public

record CertifiedSourceToObservation
    (source observation : Spatial.SpatialNode) : Set where
  constructor certifiedSourceToObservation
  field
    rawWitness : Spatial.SourceToObservationWitness source observation
    certifiedSupport : CertifiedSpatialSupport source observation
    supportMatchesRaw :
      rawSupport certifiedSupport ≡ Spatial.support rawWitness
    timingCheck : Spatial.timingCompatible rawWitness ≡ true
    attenuationCheck : Spatial.attenuationModelRecorded rawWitness ≡ true

open CertifiedSourceToObservation public

record CertifiedMachineryRoute
    {machine : Spatial.MachineryProfile}
    {origin target : Spatial.SpatialNode}
    (route : Spatial.MachineryRoute machine origin target) : Set where
  constructor certifiedMachineryRoute
  field
    slopeChecked : Spatial.slopeConstraintChecked route ≡ true
    turningChecked : Spatial.turningConstraintChecked route ≡ true
    widthChecked : Spatial.widthConstraintChecked route ≡ true
    seasonalChecked : Spatial.seasonalAccessChecked route ≡ true

open CertifiedMachineryRoute public

record CertifiedSpatialBoundary : Set where
  constructor certifiedSpatialBoundary
  field
    rawPathDoesNotImplyCertifiedEdgeChecks : Bool
    certifiedPathForgetsToRawPath : Bool
    certifiedSupportRequiresScaleSuccess : Bool
    sourceObservationPromotionRequiresTimingAndAttenuation : Bool
    machineryChecksRemainOperationalNotEcological : Bool

canonicalCertifiedSpatialBoundary : CertifiedSpatialBoundary
canonicalCertifiedSpatialBoundary =
  certifiedSpatialBoundary true true true true true
