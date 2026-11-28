module DASHI.Cognition.PNF.X369NativeNineCubeFaceWeldExact where

-- P0 SAME-OBJECT BIDI: original H07 nine-trit codec Blocks Trit
-- <-> ORIGINAL Base369 interaction + two appraisals (3*3*3 trits).
-- NOT the 5832 corner stratum, not an abstract cardinality bijection.
-- Reuse original six-face codecCube and its already-constructed witnesses.
-- Attribution: original Leech-LILA Anatolii Kornienko; DASHI extension.
-- Kernel deferred by user; no postulate, hole, or CI.
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Algebra.Trit as T
import DASHI.Codec.IndexedCubeMaskSignExact as C
import DASHI.Codec.IndexedCubeMaskSignInstanceExact as I
import DASHI.Codec.IndexedCubeHyperfibreExact as H07
import DASHI.Codec.IndexedAffineCornerAppraisal5832Exact as N
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as G
import DASHI.Core.GovernedIndexedResidualCubeExact as Q
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as F

Source : Set
Source = C.Blocks T.Trit

Full : Set
Full = G.TernaryHyperformalPoint

toNative : Source → Full
toNative (C.blocks i a b) =
  G.ternaryHyperformalPoint
    (N.tripleToPoint i)
    (N.tripleToPoint a)
    (N.tripleToPoint b)

fromNative : Full → Source
fromNative (G.ternaryHyperformalPoint i a b) =
  C.blocks
    (N.pointToTriple i)
    (N.pointToTriple a)
    (N.pointToTriple b)

nativeAfterSource : (x : Source) → fromNative (toNative x) ≡ x
nativeAfterSource (C.blocks i a b)
  rewrite N.triplePointRoundTrip i
        | N.triplePointRoundTrip a
        | N.triplePointRoundTrip b = refl

sourceAfterNative : (x : Full) → toNative (fromNative x) ≡ x
sourceAfterNative (G.ternaryHyperformalPoint i a b)
  rewrite N.pointTripleRoundTrip i
        | N.pointTripleRoundTrip a
        | N.pointTripleRoundTrip b = refl

-- The native interaction projection intentionally discards BOTH appraisal
-- cubes. Their exact BIDI is held by G.projectAppraisalFibre/rebuild.
interaction : Source → G.Ternary27Point
interaction x = G.projectInteractionVoxel (toNative x)

appraisals : Source → G.AppraisalFibrePoint
appraisals x = G.projectAppraisalFibre (toNative x)

reopen : (x : Source) →
  G.rebuildOverInteraction (interaction x) (appraisals x) ≡ toNative x
reopen (C.blocks i a b) = refl

-- Original native FULL 9-coordinate rotation is transported by genuine
-- reversible charts, not redefined as a six-coordinate signed action.
rotateNative : Full → Full
rotateNative x = toNative (C.rotate (fromNative x))

rotateNaturality : (x : Source) →
  rotateNative (toNative x) ≡ toNative (C.rotate x)
rotateNaturality x
  rewrite nativeAfterSource x = refl

decodeCubeTerminal : Source → Full
decodeCubeTerminal x =
  toNative (C.decode (C.join (Q.xyz I.codecCube x)))

-- All original six commuting faces now act on a native 19683-address
-- chart, since their endpoint witnesses are already proven by I.codecExactFaces.
sixFaceTerminal : (x : Source) →
  decodeCubeTerminal x ≡ toNative (C.rotate x)
sixFaceTerminal x = F.cong toNative (I.terminalReopen x)

cubeEndpointAgreement : (x : Source) →
  toNative (C.decode (C.join (Q.xyz I.codecCube x))) ≡
  toNative (C.decode (C.join (Q.zyx I.codecCube x)))
cubeEndpointAgreement x =
  F.cong (λ y → toNative (C.decode (C.join y))) (I.allPathsExample x)

-- A consumer can observe FULL native appraisal data: no forced reduction to
-- interaction/6 signed channels. All four terminal projections are observed
-- only after genuine source endpoint re-opening.
module Consumer {Output : Set} (observe : Full → Output) where

  terminalRespectsRotation : (x : Source) →
    observe (decodeCubeTerminal x) ≡
    observe (toNative (C.rotate x))
  terminalRespectsRotation x = F.cong observe (sixFaceTerminal x)

  routeIndependence : (x : Source) →
    observe (toNative (C.decode (C.join (Q.xyz I.codecCube x)))) ≡
    observe (toNative (C.decode (C.join (Q.zyx I.codecCube x))))
  routeIndependence x = F.cong observe (cubeEndpointAgreement x)

-- H07.indexedLocalFibre supplies history/time/version alignment of this
-- SAME codec; it certifies local faces, not arbitrary cross-time dynamics.
-- The physical 6+3 tangent, C26 indexed Singer and native graph adjacency
-- remain separate source actors; no equality is manufactured here.
