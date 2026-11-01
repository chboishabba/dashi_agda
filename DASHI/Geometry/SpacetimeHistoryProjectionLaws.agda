module DASHI.Geometry.SpacetimeHistoryProjectionLaws where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.SpacetimeHistoryWorldTube
  using (ProjectionKind; spacetimeCubeProjection; geographicLongExposureProjection;
         calendricalHelixProjection; semanticPlaceBraidProjection;
         movingPresentSliceProjection)
open import DASHI.Geometry.SpacetimeHistoryTypedCore

record CubePoint : Set where
  constructor cubePoint
  field cubeEast : Metres
        cubeNorth : Metres
        cubeTime : Timestamp
        cubeRadius : Metres
open CubePoint public

record LongExposurePoint : Set where
  constructor longExposurePoint
  field exposureEast : Metres
        exposureNorth : Metres
        exposureWeight : Nat
open LongExposurePoint public

record HelixPoint : Set where
  constructor helixPoint
  field helixEast : Metres
        helixNorth : Metres
        helixPhase : Nat
        helixCycle : Nat
open HelixPoint public

record BraidPoint : Set where
  constructor braidPoint
  field braidPlace : String
        braidOrder : Timestamp
        braidWeight : Nat
open BraidPoint public

record SlicePoint : Set where
  constructor slicePoint
  field sliceWorld : WorldCoordinate
        sliceAt : Timestamp
open SlicePoint public

piCube : TypedObservation → CubePoint
piCube o =
  cubePoint
    (eastMetres (observedWorld o))
    (northMetres (observedWorld o))
    (observedAt o)
    (uncertaintyRadius o)

piLong : TypedObservation → LongExposurePoint
piLong o =
  longExposurePoint
    (eastMetres (observedWorld o))
    (northMetres (observedWorld o))
    1

piHelix : Nat → Nat → TypedObservation → HelixPoint
piHelix phase cycle o =
  helixPoint
    (eastMetres (observedWorld o))
    (northMetres (observedWorld o))
    phase cycle

piBraid : Nat → TypedObservation → BraidPoint
piBraid weight o = braidPoint (observedPlace o) (observedAt o) weight

piSlice : Timestamp → TypedObservation → SlicePoint
piSlice t o = slicePoint (observedWorld o) t

data ProjectionOutput : Set where
  cubeOutput : CubePoint → ProjectionOutput
  longOutput : LongExposurePoint → ProjectionOutput
  helixOutput : HelixPoint → ProjectionOutput
  braidOutput : BraidPoint → ProjectionOutput
  sliceOutput : SlicePoint → ProjectionOutput

project : ProjectionKind → TypedObservation → ProjectionOutput
project spacetimeCubeProjection o = cubeOutput (piCube o)
project geographicLongExposureProjection o = longOutput (piLong o)
project calendricalHelixProjection o = helixOutput (piHelix 0 0 o)
project semanticPlaceBraidProjection o = braidOutput (piBraid 1 o)
project movingPresentSliceProjection o = sliceOutput (piSlice (observedAt o) o)

-- Long exposure intentionally forgets timestamp, confidence, source, and mode.
record LongExposureForgetsTime (o : TypedObservation) : Set where
  constructor longExposureForgetsTime
  field projected : LongExposurePoint
        projectedIsCanonical : projected ≡ piLong o
open LongExposureForgetsTime public

longExposureTimeLoss : (o : TypedObservation) → LongExposureForgetsTime o
longExposureTimeLoss o = longExposureForgetsTime (piLong o) refl

record ProjectionInformationLaw : Set where
  constructor projectionInformationLaw
  field kind : ProjectionKind
        preservesWorldPosition : Nat
        preservesTimeOrder : Nat
        preservesSourceProvenance : Nat
        preservesIdentity : Nat
open ProjectionInformationLaw public

canonicalProjectionInformationLaws : List ProjectionInformationLaw
canonicalProjectionInformationLaws =
  projectionInformationLaw spacetimeCubeProjection 1 1 0 0
  ∷ projectionInformationLaw geographicLongExposureProjection 1 0 0 0
  ∷ projectionInformationLaw calendricalHelixProjection 1 1 0 0
  ∷ projectionInformationLaw semanticPlaceBraidProjection 0 1 0 0
  ∷ projectionInformationLaw movingPresentSliceProjection 1 0 0 0
  ∷ []
