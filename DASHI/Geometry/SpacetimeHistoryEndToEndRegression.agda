module DASHI.Geometry.SpacetimeHistoryEndToEndRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

open import DASHI.Geometry.SpacetimeHistoryWorldTube
open import DASHI.Geometry.SpacetimeHistoryTypedCore
open import DASHI.Geometry.SpacetimeHistoryProjectionLaws
open import DASHI.Geometry.SpacetimeHistoryScaleHierarchy
open import DASHI.Geometry.SpacetimeHistoryRegistrationAndClustering
open import DASHI.Vision.Stereo4DDynamicReconstructionBridge
open import DASHI.Vision.GaussianVideoCompressionBridge

world : WorldCoordinate
world = worldCoordinate (metres 1) (metres 2) (metres 3) "local ENU"

observation : TypedObservation
observation =
  typedObservation 1 (timestamp 1000) world (metres 5) (confidence 900)
    walkingMode "candidate place" "timeline import"

unknown : HistorySegment
unknown = unknownGap observation observation

missingness-regression : segmentStatus unknown ≡ unknownGapInterval
missingness-regression = refl

long-exposure-regression :
  exposureEast (piLong observation) ≡ eastMetres world
long-exposure-regression = refl

non-replacement-regression :
  identityNotInherited (canonicalNonReplacement observation observation) ≡ true
non-replacement-regression = refl

place : PlaceCluster
place = placeCluster 1 "cluster" world (metres 20) (confidence 800) false refl

vendor-label-not-authority-regression :
  placeClusterVendorLabelAuthoritative place ≡ false
vendor-label-not-authority-regression = refl

seed : Gaussian2DSeed
seed = gaussian2DSeed 0 10 10 1 0 1 255 255 255

feature : MultiPlaneFeature
feature = multiPlaneFeature 0 0 (xyPlane ∷ xtPlane ∷ ytPlane ∷ []) (1 ∷ []) true refl

model : GaussianVideoModel
model =
  mkCandidateGaussianVideoModel "candidate" (seed ∷ []) (feature ∷ []) [] [] [] 8

gaussian-lossy-regression : lossy model ≡ true
gaussian-lossy-regression = refl

gaussian-no-geometry-regression : recoversGeometry model ≡ false
gaussian-no-geometry-regression = refl

gaussian-no-motion-authority-regression : physicalMotionAuthority model ≡ false
gaussian-no-motion-authority-regression = refl
