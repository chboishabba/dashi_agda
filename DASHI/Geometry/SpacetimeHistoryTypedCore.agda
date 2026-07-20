module DASHI.Geometry.SpacetimeHistoryTypedCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.SpacetimeHistoryWorldTube
  using (MotionMode; ProjectionKind)

------------------------------------------------------------------------
-- Unit-separated carrier layer.

record Timestamp : Set where
  constructor timestamp
  field epochMilliseconds : Nat
open Timestamp public

record Duration : Set where
  constructor duration
  field durationMilliseconds : Nat
open Duration public

record Metres : Set where
  constructor metres
  field metreCount : Nat
open Metres public

record Confidence : Set where
  constructor confidence
  field confidencePermille : Nat
open Confidence public

record LatitudeE7 : Set where
  constructor latitudeE7
  field signedLatitudeEncoding : Nat
open LatitudeE7 public

record LongitudeE7 : Set where
  constructor longitudeE7
  field signedLongitudeEncoding : Nat
open LongitudeE7 public

record PixelCoordinate : Set where
  constructor pixelCoordinate
  field pixelX : Nat
        pixelY : Nat
open PixelCoordinate public

record WorldCoordinate : Set where
  constructor worldCoordinate
  field eastMetres : Metres
        northMetres : Metres
        upMetres : Metres
        coordinateFrame : String
open WorldCoordinate public

record TypedObservation : Set where
  constructor typedObservation
  field observationId : Nat
        observedAt : Timestamp
        observedWorld : WorldCoordinate
        uncertaintyRadius : Metres
        observationConfidence : Confidence
        observedMode : MotionMode
        observedPlace : String
        observedSource : String
open TypedObservation public

------------------------------------------------------------------------
-- Relations are evidence objects, not string-valued claims.

data ObservedBy (o : TypedObservation) (source : String) : Set where
  observed-by : observedSource o ≡ source → ObservedBy o source

data ProjectsTo (o : TypedObservation) (kind : ProjectionKind) : Set where
  projects-to : ProjectsTo o kind

data Enriches (local : TypedObservation) (coarse : TypedObservation) : Set where
  enriches-without-replacement : Enriches local coarse

data RendersAt (o : TypedObservation) (t : Timestamp) : Set where
  renders-at : observedAt o ≡ t → RendersAt o t

record NonReplacementLaw (local coarse : TypedObservation) : Set where
  constructor nonReplacementLaw
  field
    enrichment : Enriches local coarse
    identityNotInherited : Bool
    identityNotInheritedIsTrue : identityNotInherited ≡ true
    semanticsNotInherited : Bool
    semanticsNotInheritedIsTrue : semanticsNotInherited ≡ true
open NonReplacementLaw public

canonicalNonReplacement :
  (local coarse : TypedObservation) → NonReplacementLaw local coarse
canonicalNonReplacement local coarse =
  nonReplacementLaw enriches-without-replacement true refl true refl

------------------------------------------------------------------------
-- Partial interpolation and explicit missingness.

data IntervalStatus : Set where
  observedInterval : IntervalStatus
  interpolatedInterval : IntervalStatus
  unknownGapInterval : IntervalStatus
  discontinuousTravelInterval : IntervalStatus
  conflictingInterval : IntervalStatus

data InterpolationModel : Set where
  holdPositionModel : InterpolationModel
  linearWorldModel : InterpolationModel
  routeConstrainedModel : InterpolationModel
  noInterpolationModel : InterpolationModel

record InterpolationPolicy : Set where
  constructor interpolationPolicy
  field maximumGap : Duration
        minimumConfidence : Confidence
        model : InterpolationModel
open InterpolationPolicy public

record HistorySegment : Set where
  constructor historySegment
  field segmentStart : TypedObservation
        segmentEnd : TypedObservation
        segmentStatus : IntervalStatus
        segmentModel : InterpolationModel
        segmentInventsObservation : Bool
        segmentInventsObservationIsFalse : segmentInventsObservation ≡ false
open HistorySegment public

unknownGap : TypedObservation → TypedObservation → HistorySegment
unknownGap a b = historySegment a b unknownGapInterval noInterpolationModel false refl

interpolatedSegment :
  TypedObservation → TypedObservation → InterpolationModel → HistorySegment
interpolatedSegment a b m =
  historySegment a b interpolatedInterval m false refl

interpolate :
  InterpolationPolicy → Bool → TypedObservation → TypedObservation → Maybe HistorySegment
interpolate policy admissible a b with admissible
... | true = just (interpolatedSegment a b (model policy))
... | false = nothing

missingRemainsMissing :
  (a b : TypedObservation) →
  segmentStatus (unknownGap a b) ≡ unknownGapInterval
missingRemainsMissing a b = refl

canonicalTypedCoreNotes : List String
canonicalTypedCoreNotes =
  "Timestamp and duration are distinct carriers"
  ∷ "Pixel and world coordinates are distinct carriers"
  ∷ "Confidence and uncertainty radius are distinct carriers"
  ∷ "Interpolation is partial and policy-governed"
  ∷ "Unknown gaps do not manufacture observations"
  ∷ "Enrichment does not inherit identity or semantics"
  ∷ []
