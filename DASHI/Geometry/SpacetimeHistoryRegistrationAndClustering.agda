module DASHI.Geometry.SpacetimeHistoryRegistrationAndClustering where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.SpacetimeHistoryTypedCore
open import DASHI.Geometry.SpacetimeHistoryScaleHierarchy

record PlaceCluster : Set where
  constructor placeCluster
  field placeClusterId : Nat
        placeClusterLabel : String
        placeClusterCentre : WorldCoordinate
        placeClusterRadius : Metres
        placeClusterConfidence : Confidence
        placeClusterVendorLabelAuthoritative : Bool
        placeClusterVendorLabelAuthoritativeIsFalse :
          placeClusterVendorLabelAuthoritative ≡ false
open PlaceCluster public

record ClusterMembership (o : TypedObservation) (cluster : PlaceCluster) : Set where
  constructor clusterMembership
  field membershipDistance : Metres
        membershipWithinRadius : Bool
        membershipWithinRadiusIsTrue : membershipWithinRadius ≡ true
        membershipInferred : Bool
open ClusterMembership public

record VideoAsset : Set where
  constructor videoAsset
  field videoReference : String
        videoStart : Timestamp
        videoEnd : Timestamp
        videoCoordinateFrame : String
        videoPoseReference : String
open VideoAsset public

record RegistrationReceipt : Set where
  constructor registrationReceipt
  field registeredVideo : VideoAsset
        registeredEpisode : VisualEpisode
        timeOverlapEstablished : Bool
        timeOverlapEstablishedIsTrue : timeOverlapEstablished ≡ true
        coordinateAlignmentEstablished : Bool
        coordinateAlignmentEstablishedIsTrue : coordinateAlignmentEstablished ≡ true
        provenancePreserved : Bool
        provenancePreservedIsTrue : provenancePreserved ≡ true
        registrationExact : Bool
        registrationExactIsFalse : registrationExact ≡ false
        registrationReplacesHistory : Bool
        registrationReplacesHistoryIsFalse : registrationReplacesHistory ≡ false
open RegistrationReceipt public

mkCandidateRegistration : VideoAsset → VisualEpisode → RegistrationReceipt
mkCandidateRegistration video episode =
  registrationReceipt video episode true refl true refl true refl false refl false refl

record PaperIntegrationBoundary : Set where
  constructor paperIntegrationBoundary
  field paperTitle : String
        paperReference : String
        integrationRole : String
        implementationVerified : Bool
        implementationVerifiedIsFalse : implementationVerified ≡ false
        physicalMotionAuthority : Bool
        physicalMotionAuthorityIsFalse : physicalMotionAuthority ≡ false
open PaperIntegrationBoundary public

stereo4DBoundary : PaperIntegrationBoundary
stereo4DBoundary =
  paperIntegrationBoundary
    "Stereo4D: Learning How Things Move in 3D from Internet Stereo Videos"
    "Jin et al., arXiv:2412.09621v1 (2024)"
    "candidate pseudo-metric local dynamic-scene reconstruction"
    false refl false refl

gaussianVideoBoundary : PaperIntegrationBoundary
gaussianVideoBoundary =
  paperIntegrationBoundary
    "GaussianVideo: Efficient Video Representation and Compression by Gaussian Splatting"
    "Lee, Choi, and Lee, arXiv:2503.04333v1 (2025)"
    "candidate lossy time-conditioned image-plane representation"
    false refl false refl

canonicalRegistrationNotes : List String
canonicalRegistrationNotes =
  "Place clustering is uncertainty-aware and does not treat vendor labels as authoritative"
  ∷ "Video registration requires both temporal overlap and coordinate alignment"
  ∷ "Registration preserves provenance and remains non-exact"
  ∷ "Stereo4D scene motion is not automatically subject motion"
  ∷ "GaussianVideo latent deformation is not automatically physical motion"
  ∷ []
