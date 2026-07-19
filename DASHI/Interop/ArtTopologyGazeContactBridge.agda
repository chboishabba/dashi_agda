module DASHI.Interop.ArtTopologyGazeContactBridge where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Topology.VisualPersistentHomologyCore as PH

------------------------------------------------------------------------
-- Observable-contact bridge between image topology and gaze maps.
--
-- Contact means that a source-bound topological feature map and a gaze map
-- refer to the same spatial cell.  It does not recover artist intent, cause
-- aesthetic experience, or turn correlation into a universal perceptual law.

data TopologicalFeatureKind : Set where
  persistenceFeature : TopologicalFeatureKind
  cycleDensityFeature : TopologicalFeatureKind
  cyclePerimeterFeature : TopologicalFeatureKind

record TopologicalFeatureCell : Set where
  constructor mkTopologicalFeatureCell
  field
    featureRegion : String
    featureKind : TopologicalFeatureKind
    featureFiltration : PH.FiltrationDirection
    featureDimension : PH.HomologyDimension
    featureMagnitude : Nat

open TopologicalFeatureCell public

record GazeFixationCell : Set where
  constructor mkGazeFixationCell
  field
    gazeRegion : String
    fixationCount : Nat
    fixationDurationBucket : Nat

open GazeFixationCell public

record FeatureGazeContact : Set where
  constructor mkFeatureGazeContact
  field
    featureCell : TopologicalFeatureCell
    gazeCell : GazeFixationCell
    contactRegion : String
    featureRegionMatches :
      featureRegion featureCell ≡ contactRegion
    gazeRegionMatches :
      gazeRegion gazeCell ≡ contactRegion

open FeatureGazeContact public

record ArtTopologyGazeContactBridge
    (signature : PH.ImagePersistenceSignature) : Set where
  constructor mkArtTopologyGazeContactBridge
  field
    featureMap : List TopologicalFeatureCell
    gazeMap : List GazeFixationCell
    observedContacts : List FeatureGazeContact

    contactImpliesCausation : Bool
    contactImpliesCausationIsFalse :
      contactImpliesCausation ≡ false

    contactImpliesAestheticValue : Bool
    contactImpliesAestheticValueIsFalse :
      contactImpliesAestheticValue ≡ false

    contactRecoversArtistIntent : Bool
    contactRecoversArtistIntentIsFalse :
      contactRecoversArtistIntent ≡ false

    galleryAndLaboratoryAreInterchangeable : Bool
    galleryAndLaboratoryAreInterchangeableIsFalse :
      galleryAndLaboratoryAreInterchangeable ≡ false

    authorityBundle : Authority.AuthorityNonPromotionBundle
    scientificAuthorityIsFalse :
      Authority.authorityFlag
        Authority.scientificAuthority authorityBundle
      ≡ false
    empiricalAuthorityIsFalse :
      Authority.authorityFlag
        Authority.empiricalAuthority authorityBundle
      ≡ false

open ArtTopologyGazeContactBridge public

closedArtTopologyGazeAuthority :
  Authority.AuthorityNonPromotionBundle
closedArtTopologyGazeAuthority =
  Authority.mkClosedAuthorityNonPromotionBundle
    "art topology / gaze contact: source-bound correlation without causal or aesthetic promotion"

emptyArtTopologyGazeContactBridge :
  (signature : PH.ImagePersistenceSignature) →
  ArtTopologyGazeContactBridge signature
emptyArtTopologyGazeContactBridge signature =
  mkArtTopologyGazeContactBridge
    []
    []
    []
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    closedArtTopologyGazeAuthority
    (Authority.authorityFlagIsFalse
      Authority.scientificAuthority
      closedArtTopologyGazeAuthority)
    (Authority.authorityFlagIsFalse
      Authority.empiricalAuthority
      closedArtTopologyGazeAuthority)
