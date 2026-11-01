module DASHI.Physics.Textile.TextileReflectiveDiffractiveOpticalTrainExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Interop.StationaryPhaseMirrorGratingToyReceipt as MirrorGrating
import DASHI.Physics.Textile.TextileOpticalTransportBridgeExact as Optical
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch

------------------------------------------------------------------------
-- Reuse the repository's existing stationary-phase mirror/grating toy lane as
-- an external illumination/observation-path coordinate around a textile.
-- This is intentionally separate from intrinsic textile reflection/diffraction.
------------------------------------------------------------------------

data ReflectiveDiffractiveElementKind : Set where
  stationaryPhaseMirror : ReflectiveDiffractiveElementKind
  gratingMask : ReflectiveDiffractiveElementKind

setupKind : ReflectiveDiffractiveElementKind → MirrorGrating.StationaryPhaseToySetup
setupKind stationaryPhaseMirror = MirrorGrating.mirrorFermatToySetup
setupKind gratingMask = MirrorGrating.gratingMaskToySetup

record TextileReflectiveDiffractivePath
    {OpticalState Illumination OpticalObserver Radiance : Set}
    {topology : Stitch.StitchState}
    (model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology) : Set₁ where
  constructor textile-reflective-diffractive-path
  field
    elementKind : ReflectiveDiffractiveElementKind
    opticalSetupDescription : String
    retainedTextileModel :
      Optical.TextileOpticalModel
        OpticalState Illumination OpticalObserver Radiance topology
    retainedTextileModelIsSameObject : retainedTextileModel ≡ model

open TextileReflectiveDiffractivePath public

record StationaryPhasePathReceipt
    {OpticalState Illumination OpticalObserver Radiance : Set}
    {topology : Stitch.StitchState}
    {model : Optical.TextileOpticalModel
      OpticalState Illumination OpticalObserver Radiance topology}
    (path : TextileReflectiveDiffractivePath model) : Set₁ where
  constructor stationary-phase-path-receipt
  field
    setup : MirrorGrating.StationaryPhaseToySetup
    setupMatchesElementKind : setup ≡ setupKind (elementKind path)
    stationaryPhaseApproximationEvidence : String
    residualBoundEvidence : String

open StationaryPhasePathReceipt public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data ExternalMirrorIsIntrinsicTextileSpecularResponse : Set where
externalMirrorIsNotIntrinsicTextileSpecularResponse :
  ExternalMirrorIsIntrinsicTextileSpecularResponse → ⊥
externalMirrorIsNotIntrinsicTextileSpecularResponse ()

data ExternalGratingProvesTextileDiffractiveMicrostructure : Set where
externalGratingDoesNotProveTextileDiffractiveMicrostructure :
  ExternalGratingProvesTextileDiffractiveMicrostructure → ⊥
externalGratingDoesNotProveTextileDiffractiveMicrostructure ()

data ToyStationaryPhaseReceiptIsFullRenderer : Set where
toyStationaryPhaseReceiptIsNotFullRenderer : ToyStationaryPhaseReceiptIsFullRenderer → ⊥
toyStationaryPhaseReceiptIsNotFullRenderer ()
