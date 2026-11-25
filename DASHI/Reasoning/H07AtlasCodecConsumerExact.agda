module DASHI.Reasoning.H07AtlasCodecConsumerExact where

-- Literal original H05 codec faces, with a full marked-affine observation.
-- The independent frame is not erased by partition or support/sign encoding.
open import DASHI.Core.Prelude
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
import DASHI.Codec.TriadicMaskSignFactorization as M
import DASHI.Codec.IndexedCubeMaskSignExact as C
import DASHI.Codec.IndexedCubeMaskSignInstanceExact as I
import DASHI.Codec.IndexedCubeAffinePivotOverlapExact as O
import DASHI.Codec.IndexedCubeAffineStableOverlapExact as Stable
import DASHI.Codec.IndexedCubePivot02RechartedExact as Pivot
import DASHI.Codec.IndexedAffineCornerAppraisalConsumerTransportExact as Native
import DASHI.Codec.IndexedAffineNativeGraphTransportExact as Graph
import DASHI.Core.GovernedIndexedResidualCubeExact as Q
import DASHI.Core.GovernedDiagramCore as G
import DASHI.Reasoning.H07FullAtlasSectionExact as H
import DASHI.Reasoning.H07AffinePairedSeamExact as S
import DASHI.Reasoning.H07AtlasRotationNaturalityExact as R

directionOf : H.Pivot → C.Blocks Trit → H.Direction
directionOf H.p01 (C.blocks (M.triple a0 b0 c0) (M.triple a1 b1 c1) r) =
  H.direction (H.vec5 pos zer a0 b0 c0) (H.vec5 zer pos a1 b1 c1)
directionOf H.p02 (C.blocks (M.triple a0 b0 c0) (M.triple a1 b1 c1) r) =
  H.direction (H.vec5 pos a0 zer b0 c0) (H.vec5 zer a1 pos b1 c1)
directionOf H.p03 (C.blocks (M.triple a0 b0 c0) (M.triple a1 b1 c1) r) =
  H.direction (H.vec5 pos a0 b0 zer c0) (H.vec5 zer a1 b1 pos c1)
directionOf H.p04 (C.blocks (M.triple a0 b0 c0) (M.triple a1 b1 c1) r) =
  H.direction (H.vec5 pos a0 b0 c0 zer) (H.vec5 zer a1 b1 c1 pos)
directionOf H.p12 (C.blocks (M.triple a0 b0 c0) (M.triple a1 b1 c1) r) =
  H.direction (H.vec5 a0 pos zer b0 c0) (H.vec5 a1 zer pos b1 c1)
directionOf H.p13 (C.blocks (M.triple a0 b0 c0) (M.triple a1 b1 c1) r) =
  H.direction (H.vec5 a0 pos b0 zer c0) (H.vec5 a1 zer b1 pos c1)
directionOf H.p14 (C.blocks (M.triple a0 b0 c0) (M.triple a1 b1 c1) r) =
  H.direction (H.vec5 a0 pos b0 c0 zer) (H.vec5 a1 zer b1 c1 pos)
directionOf H.p23 (C.blocks (M.triple a0 b0 c0) (M.triple a1 b1 c1) r) =
  H.direction (H.vec5 a0 b0 pos zer c0) (H.vec5 a1 b1 zer pos c1)
directionOf H.p24 (C.blocks (M.triple a0 b0 c0) (M.triple a1 b1 c1) r) =
  H.direction (H.vec5 a0 b0 pos c0 zer) (H.vec5 a1 b1 zer c1 pos)
directionOf H.p34 (C.blocks (M.triple a0 b0 c0) (M.triple a1 b1 c1) r) =
  H.direction (H.vec5 a0 b0 c0 pos zer) (H.vec5 a1 b1 c1 zer pos)

offsetOf : H.Pivot → C.Blocks Trit → H.Vec5
offsetOf H.p01 (C.blocks u v (M.triple a2 b2 c2)) = (H.vec5 zer zer a2 b2 c2)
offsetOf H.p02 (C.blocks u v (M.triple a2 b2 c2)) = (H.vec5 zer a2 zer b2 c2)
offsetOf H.p03 (C.blocks u v (M.triple a2 b2 c2)) = (H.vec5 zer a2 b2 zer c2)
offsetOf H.p04 (C.blocks u v (M.triple a2 b2 c2)) = (H.vec5 zer a2 b2 c2 zer)
offsetOf H.p12 (C.blocks u v (M.triple a2 b2 c2)) = (H.vec5 a2 zer zer b2 c2)
offsetOf H.p13 (C.blocks u v (M.triple a2 b2 c2)) = (H.vec5 a2 zer b2 zer c2)
offsetOf H.p14 (C.blocks u v (M.triple a2 b2 c2)) = (H.vec5 a2 zer b2 c2 zer)
offsetOf H.p23 (C.blocks u v (M.triple a2 b2 c2)) = (H.vec5 a2 b2 zer zer c2)
offsetOf H.p24 (C.blocks u v (M.triple a2 b2 c2)) = (H.vec5 a2 b2 zer c2 zer)
offsetOf H.p34 (C.blocks u v (M.triple a2 b2 c2)) = (H.vec5 a2 b2 c2 zer zer)

anchorOf : (p : H.Pivot) (x : C.Blocks Trit) → H.Mark (directionOf p x)
anchorOf H.p01 (C.blocks (M.triple a b c) (M.triple d e f) r) = H.mark H.p01 O.positive
anchorOf H.p02 (C.blocks (M.triple a b c) (M.triple d e f) r) = H.mark H.p02 O.positive
anchorOf H.p03 (C.blocks (M.triple a b c) (M.triple d e f) r) = H.mark H.p03 O.positive
anchorOf H.p04 (C.blocks (M.triple a b c) (M.triple d e f) r) = H.mark H.p04 O.positive
anchorOf H.p12 (C.blocks (M.triple a b c) (M.triple d e f) r) = H.mark H.p12 O.positive
anchorOf H.p13 (C.blocks (M.triple a b c) (M.triple d e f) r) = H.mark H.p13 O.positive
anchorOf H.p14 (C.blocks (M.triple a b c) (M.triple d e f) r) = H.mark H.p14 O.positive
anchorOf H.p23 (C.blocks (M.triple a b c) (M.triple d e f) r) = H.mark H.p23 O.positive
anchorOf H.p24 (C.blocks (M.triple a b c) (M.triple d e f) r) = H.mark H.p24 O.positive
anchorOf H.p34 (C.blocks (M.triple a b c) (M.triple d e f) r) = H.mark H.p34 O.positive

findMark : (L : H.Direction) (p : H.Pivot) → Maybe (H.Mark L)
findMark L p with H.determinant L p in eq
... | neg = just (H.mark p (subst O.Nonzero (sym eq) O.negative))
... | zer = nothing
... | pos = just (H.mark p (subst O.Nonzero (sym eq) O.positive))

record Frame : Set where
  constructor frame
  field
    anchor localMark targetMark : H.Pivot
    winding : Trit
    context : S.Context

record Payload : Set where
  constructor payload
  field
    localRaw signedCorrection commonRestriction : H.Vec5

-- Source, frame and explicit refused singular case survive in the output.
record Observation : Set where
  constructor observation
  field
    source : C.Blocks Trit
    originalFrame : Frame
    readout : Maybe Payload

observe : Frame → C.Blocks Trit → Observation
observe k@(frame p v q n ctx) x with findMark (directionOf p x) v | findMark (directionOf p x) q
... | just v′ | just q′ =
  observation x k (just (payload
    (H.raw v′ (offsetOf p x) n)
    (H.correction (anchorOf p x) v′ n)
    (H.Shared.normalized (H.restrict {q = q′} H.sameDirection
      (H.local (H.raw v′ (offsetOf p x) n)
        (H.correction (anchorOf p x) v′ n) n ctx)))))
... | _ | _ = observation x k nothing

reopenSplit : C.PrefixResidual Trit → C.Blocks Trit
reopenSplit = C.join

reopenFact : C.Blocks M.FactorizedTrit → C.Blocks Trit
reopenFact = C.decode

reopenFactSplit : C.PrefixResidual M.FactorizedTrit → C.Blocks Trit
reopenFactSplit x = C.decode (C.join x)

observexy0 : (k : Frame) (x : Q.A I.codecCube) →
  observe k (reopenSplit (Q.y10 I.codecCube (Q.x00 I.codecCube x))) ≡
  observe k (reopenSplit (Q.x10 I.codecCube (Q.y00 I.codecCube x)))
observexy0 k x = cong (λ z → observe k (reopenSplit z))
  (G.commutes (Q.pxy0 I.codecExactFaces) x)

observexz0 : (k : Frame) (x : Q.A I.codecCube) →
  observe k (reopenFactSplit (Q.z10 I.codecCube (Q.x00 I.codecCube x))) ≡
  observe k (reopenFactSplit (Q.x01 I.codecCube (Q.z00 I.codecCube x)))
observexz0 k x = cong (λ z → observe k (reopenFactSplit z))
  (G.commutes (Q.pxz0 I.codecExactFaces) x)

observeyz0 : (k : Frame) (x : Q.A I.codecCube) →
  observe k (reopenFact (Q.z01 I.codecCube (Q.y00 I.codecCube x))) ≡
  observe k (reopenFact (Q.y01 I.codecCube (Q.z00 I.codecCube x)))
observeyz0 k x = cong (λ z → observe k (reopenFact z))
  (G.commutes (Q.pyz0 I.codecExactFaces) x)

observexy1 : (k : Frame) (x : Q.E I.codecCube) →
  observe k (reopenFactSplit (Q.y11 I.codecCube (Q.x01 I.codecCube x))) ≡
  observe k (reopenFactSplit (Q.x11 I.codecCube (Q.y01 I.codecCube x)))
observexy1 k x = cong (λ z → observe k (reopenFactSplit z))
  (G.commutes (Q.pxy1 I.codecExactFaces) x)

observexz1 : (k : Frame) (x : Q.C I.codecCube) →
  observe k (reopenFactSplit (Q.z11 I.codecCube (Q.x10 I.codecCube x))) ≡
  observe k (reopenFactSplit (Q.x11 I.codecCube (Q.z01 I.codecCube x)))
observexz1 k x = cong (λ z → observe k (reopenFactSplit z))
  (G.commutes (Q.pxz1 I.codecExactFaces) x)

observeyz1 : (k : Frame) (x : Q.B I.codecCube) →
  observe k (reopenFactSplit (Q.z11 I.codecCube (Q.y10 I.codecCube x))) ≡
  observe k (reopenFactSplit (Q.y11 I.codecCube (Q.z10 I.codecCube x)))
observeyz1 k x = cong (λ z → observe k (reopenFactSplit z))
  (G.commutes (Q.pyz1 I.codecExactFaces) x)

observeXYZ-xzy : (k : Frame) (x : C.Blocks Trit) →
  observe k (reopenFactSplit (Q.xyz I.codecCube x)) ≡
  observe k (reopenFactSplit (Q.xzy I.codecCube x))
observeXYZ-xzy k x = cong (λ z → observe k (reopenFactSplit z))
  (Q.xyz-xzy I.codecExactFaces x)

observeXYZ-yxz : (k : Frame) (x : C.Blocks Trit) →
  observe k (reopenFactSplit (Q.xyz I.codecCube x)) ≡
  observe k (reopenFactSplit (Q.yxz I.codecCube x))
observeXYZ-yxz k x = cong (λ z → observe k (reopenFactSplit z))
  (Q.xyz-yxz I.codecExactFaces x)

observeXYZ-yzx : (k : Frame) (x : C.Blocks Trit) →
  observe k (reopenFactSplit (Q.xyz I.codecCube x)) ≡
  observe k (reopenFactSplit (Q.yzx I.codecCube x))
observeXYZ-yzx k x = cong (λ z → observe k (reopenFactSplit z))
  (Q.xyz-yzx I.codecExactFaces x)

observeXYZ-zxy : (k : Frame) (x : C.Blocks Trit) →
  observe k (reopenFactSplit (Q.xyz I.codecCube x)) ≡
  observe k (reopenFactSplit (Q.zxy I.codecCube x))
observeXYZ-zxy k x = cong (λ z → observe k (reopenFactSplit z))
  (Q.xyz-zxy I.codecExactFaces x)

observeXYZ-zyx : (k : Frame) (x : C.Blocks Trit) →
  observe k (reopenFactSplit (Q.xyz I.codecCube x)) ≡
  observe k (reopenFactSplit (Q.zyx I.codecCube x))
observeXYZ-zyx k x = cong (λ z → observe k (reopenFactSplit z))
  (Q.xyz-zyx I.codecExactFaces x)

rotateFrame : Frame → Frame
rotateFrame (frame p v q n k) =
  frame p (H.rotatePivot p v) (H.rotatePivot p q) n k

-- Final observation reopens the actual rotated coefficients, with the
-- actual transported target/local marks. No extra cube or endpoint alias.
terminalObservation : (k : Frame) (x : C.Blocks Trit) →
  observe (rotateFrame k) (reopenFactSplit (Q.xyz I.codecCube x))
    ≡ observe (rotateFrame k) (C.rotate x)
terminalObservation k x = cong (observe (rotateFrame k)) (I.terminalReopen x)

directionRotates : (p : H.Pivot) (x : C.Blocks Trit) →
  directionOf p (C.rotate x) ≡ H.rotateDirection p (directionOf p x)
directionRotates H.p01 (C.blocks (M.triple a b c) (M.triple d e f) r) = refl
directionRotates H.p02 (C.blocks (M.triple a b c) (M.triple d e f) r) = refl
directionRotates H.p03 (C.blocks (M.triple a b c) (M.triple d e f) r) = refl
directionRotates H.p04 (C.blocks (M.triple a b c) (M.triple d e f) r) = refl
directionRotates H.p12 (C.blocks (M.triple a b c) (M.triple d e f) r) = refl
directionRotates H.p13 (C.blocks (M.triple a b c) (M.triple d e f) r) = refl
directionRotates H.p14 (C.blocks (M.triple a b c) (M.triple d e f) r) = refl
directionRotates H.p23 (C.blocks (M.triple a b c) (M.triple d e f) r) = refl
directionRotates H.p24 (C.blocks (M.triple a b c) (M.triple d e f) r) = refl
directionRotates H.p34 (C.blocks (M.triple a b c) (M.triple d e f) r) = refl

offsetRotates : (p : H.Pivot) (x : C.Blocks Trit) →
  offsetOf p (C.rotate x) ≡ H.rotateVec p (offsetOf p x)
offsetRotates H.p01 (C.blocks u v (M.triple a b c)) = refl
offsetRotates H.p02 (C.blocks u v (M.triple a b c)) = refl
offsetRotates H.p03 (C.blocks u v (M.triple a b c)) = refl
offsetRotates H.p04 (C.blocks u v (M.triple a b c)) = refl
offsetRotates H.p12 (C.blocks u v (M.triple a b c)) = refl
offsetRotates H.p13 (C.blocks u v (M.triple a b c)) = refl
offsetRotates H.p14 (C.blocks u v (M.triple a b c)) = refl
offsetRotates H.p23 (C.blocks u v (M.triple a b c)) = refl
offsetRotates H.p24 (C.blocks u v (M.triple a b c)) = refl
offsetRotates H.p34 (C.blocks u v (M.triple a b c)) = refl

-- Exact original restricted native graph and consumer specializations.
nativeObserverRecovers : {Outcome : Set} (consume : Native.Source → Outcome)
  (x : Native.Source) → Native.transportedObserver consume (Pivot.pivotRaw x) ≡ consume x
nativeObserverRecovers = Native.transportedObserverRecovers Pivot.selectedPivotInvolution

nativeEdgeMoves : (a b : Graph.Source) → Graph.NativeEdge a b →
  Graph.PivotEdge (Pivot.pivotRaw a) (Pivot.pivotRaw b)
nativeEdgeMoves = Graph.sourceEdgeMovesToPivot Pivot.selectedPivotInvolution

-- R.rotateRestriction is the existing dependent naturality proof for
-- admissible marks. The above cube comparison is an observation of the
-- actual source faces, not identification of the ten pivots with the
-- six spatial boundary faces. No kernel acceptance claimed.
