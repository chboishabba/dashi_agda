module DASHI.Geometry.SpacetimeHistoryScaleHierarchy where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.SpacetimeHistoryTypedCore

record PointTrack : Set where
  constructor pointTrack
  field pointTrackObservations : List TypedObservation
open PointTrack public

record DynamicScene : Set where
  constructor dynamicScene
  field sceneName : String
        sceneTracks : List PointTrack
open DynamicScene public

record VisualEpisode : Set where
  constructor visualEpisode
  field episodeName : String
        episodeScenes : List DynamicScene
        episodeStart : Timestamp
        episodeEnd : Timestamp
open VisualEpisode public

record LongitudinalHistory : Set where
  constructor longitudinalHistory
  field historyName : String
        historyEpisodes : List VisualEpisode
        historyObservations : List TypedObservation
open LongitudinalHistory public

R-point→scene : String → PointTrack → DynamicScene
R-point→scene name track = dynamicScene name (track ∷ [])

R-scene→episode : String → Timestamp → Timestamp → DynamicScene → VisualEpisode
R-scene→episode name start end scene = visualEpisode name (scene ∷ []) start end

R-episode→history : String → VisualEpisode → List TypedObservation → LongitudinalHistory
R-episode→history name episode observations =
  longitudinalHistory name (episode ∷ []) observations

record CoarseObservable : Set where
  constructor coarseObservable
  field observableName : String
        observableValue : Nat
open CoarseObservable public

record ApproximateCommutationReceipt : Set where
  constructor approximateCommutationReceipt
  field fineRoute : String
        coarseRoute : String
        observableBefore : CoarseObservable
        observableAfter : CoarseObservable
        tolerance : Nat
        representationStable : Bool
        representationStableIsTrue : representationStable ≡ true
open ApproximateCommutationReceipt public

mkApproximateCommutationReceipt :
  String → String → CoarseObservable → CoarseObservable → Nat →
  ApproximateCommutationReceipt
mkApproximateCommutationReceipt fine coarse before after tolerance =
  approximateCommutationReceipt fine coarse before after tolerance true refl

canonicalHierarchyNotes : List String
canonicalHierarchyNotes =
  "Point tracks aggregate into dynamic scenes"
  ∷ "Dynamic scenes aggregate into bounded visual episodes"
  ∷ "Visual episodes attach to a longitudinal history without replacing it"
  ∷ "Cross-scale compatibility is approximate observable stability, not equality of carriers"
  ∷ []
