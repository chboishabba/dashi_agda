module DASHI.Codec.IndexedAffineCornerAppraisal5832Exact where

-- Reuse actual Base369 geometry for the same finite cardinal 5832.
-- This is a two-sided ADDRESS chart, not a theorem that the affine
-- pivot operator is a native nearest-neighbour grid automorphism.
-- Original owners: StableOverlap, CornerEight, HypervoxelFabricGeometry,
-- SSPTritCarrier and StratifiedAppraisalFibre.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import DASHI.Algebra.Trit using (Trit)
import DASHI.Codec.TriadicMaskSignFactorization as M
import DASHI.Codec.IndexedCubeAffineStableOverlapExact as Stable
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27CornerEightExact as Corners
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geo

signToOuter : M.Sign → Corners.OuterSign
signToOuter M.negative = Corners.negativeOuter
signToOuter M.positive = Corners.positiveOuter

outerToSign : Corners.OuterSign → M.Sign
outerToSign Corners.negativeOuter = M.negative
outerToSign Corners.positiveOuter = M.positive

signRoundTrip : (s : M.Sign) →
  outerToSign (signToOuter s) ≡ s
signRoundTrip M.negative = refl
signRoundTrip M.positive = refl

outerRoundTrip : (s : Corners.OuterSign) →
  signToOuter (outerToSign s) ≡ s
outerRoundTrip Corners.negativeOuter = refl
outerRoundTrip Corners.positiveOuter = refl

tripleToPoint : M.Triple Trit → Geo.Ternary27Point
tripleToPoint (M.triple a b c) =
  Geo.ternary27Point (SSP.fromTrit a) (SSP.fromTrit b) (SSP.fromTrit c)

pointToTriple : Geo.Ternary27Point → M.Triple Trit
pointToTriple (Geo.ternary27Point a b c) =
  M.triple (SSP.toTrit a) (SSP.toTrit b) (SSP.toTrit c)

triplePointRoundTrip : (t : M.Triple Trit) →
  pointToTriple (tripleToPoint t) ≡ t
triplePointRoundTrip (M.triple a b c)
  rewrite SSP.toTrit-fromTrit a
        | SSP.toTrit-fromTrit b
        | SSP.toTrit-fromTrit c = refl

pointTripleRoundTrip : (t : Geo.Ternary27Point) →
  tripleToPoint (pointToTriple t) ≡ t
pointTripleRoundTrip (Geo.ternary27Point a b c)
  rewrite SSP.fromTrit-toTrit a
        | SSP.fromTrit-toTrit b
        | SSP.fromTrit-toTrit c = refl

tripleToCorner : M.Triple M.Sign → Corners.Corner3
tripleToCorner (M.triple a b c) =
  Corners.corner3 (signToOuter a) (signToOuter b) (signToOuter c)

cornerToTriple : Corners.Corner3 → M.Triple M.Sign
cornerToTriple (Corners.corner3 a b c) =
  M.triple (outerToSign a) (outerToSign b) (outerToSign c)

tripleCornerRoundTrip : (t : M.Triple M.Sign) →
  cornerToTriple (tripleToCorner t) ≡ t
tripleCornerRoundTrip (M.triple a b c)
  rewrite signRoundTrip a | signRoundTrip b | signRoundTrip c = refl

cornerTripleRoundTrip : (c : Corners.Corner3) →
  tripleToCorner (cornerToTriple c) ≡ c
cornerTripleRoundTrip (Corners.corner3 a b c)
  rewrite outerRoundTrip a | outerRoundTrip b | outerRoundTrip c = refl

-- Exact source 8 x 729, not the separate pointed 8 x 90 + 9.
NativeCornerAppraisal : Set
NativeCornerAppraisal = Corners.Corner3 × Geo.AppraisalFibrePoint

toNativeCornerAppraisal :
  Stable.StableBlocks Trit → NativeCornerAppraisal
toNativeCornerAppraisal (Stable.stableBlocks a slope b) =
  tripleToCorner slope ,
  Geo.appraisalFibrePoint (tripleToPoint a) (tripleToPoint b)

fromNativeCornerAppraisal :
  NativeCornerAppraisal → Stable.StableBlocks Trit
fromNativeCornerAppraisal
  (corner , Geo.appraisalFibrePoint a b) =
  Stable.stableBlocks (pointToTriple a)
    (cornerToTriple corner) (pointToTriple b)

nativeAfterStable : (x : Stable.StableBlocks Trit) →
  fromNativeCornerAppraisal (toNativeCornerAppraisal x) ≡ x
nativeAfterStable (Stable.stableBlocks a slope b)
  rewrite triplePointRoundTrip a
        | tripleCornerRoundTrip slope
        | triplePointRoundTrip b = refl

stableAfterNative : (x : NativeCornerAppraisal) →
  toNativeCornerAppraisal (fromNativeCornerAppraisal x) ≡ x
stableAfterNative (corner , Geo.appraisalFibrePoint a b)
  rewrite cornerTripleRoundTrip corner
        | pointTripleRoundTrip a
        | pointTripleRoundTrip b = refl

-- Embed in the ORIGINAL Base369 three-cube fabric, not a new 5832 type.
toFabric : Stable.StableBlocks Trit → Geo.TernaryHyperformalPoint
toFabric x with toNativeCornerAppraisal x
... | corner , fibre =
  Geo.rebuildOverInteraction (Corners.cornerPoint corner) fibre

-- This identifies the cardinal carriers and their chosen addresses,
-- while preserving the distinction between the 3^6 appraisal FIBRE
-- and the 2^3 corner STRATUM. Consumer/action intertwining is not inferred.
