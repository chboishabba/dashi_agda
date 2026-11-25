module DASHI.Reasoning.H07FullAtlasSectionExact where

-- Literal F3^5 projection and an indexed global-section consumer.
-- The two general field identities are explicit proof inputs, not postulates.
-- Finite executable acceptance: scripts/check_h07_atlas_section.py.
-- Source-written; kernel validation and all-atlas proof inhabitation open.

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)
import DASHI.Codec.IndexedCubeMarkedAffine9Exact as A
import DASHI.Codec.IndexedCubeAffinePivotOverlapExact as O
import DASHI.Reasoning.TypedHyperfabricCore as F
import DASHI.Reasoning.H07AffinePairedSeamExact as S

data Axis : Set where
  a0 a1 a2 a3 a4 : Axis

data Pivot : Set where
  p01 p02 p03 p04 p12 p13 p14 p23 p24 p34 : Pivot

first second : Pivot → Axis
first p01 = a0
first p02 = a0
first p03 = a0
first p04 = a0
first p12 = a1
first p13 = a1
first p14 = a1
first p23 = a2
first p24 = a2
first p34 = a3
second p01 = a1
second p02 = a2
second p03 = a3
second p04 = a4
second p12 = a2
second p13 = a3
second p14 = a4
second p23 = a3
second p24 = a4
second p34 = a4

record Vec5 : Set where
  constructor vec5
  field
    c0 c1 c2 c3 c4 : Trit

at : Axis → Vec5 → Trit
at a0 = Vec5.c0
at a1 = Vec5.c1
at a2 = Vec5.c2
at a3 = Vec5.c3
at a4 = Vec5.c4

add : Vec5 → Vec5 → Vec5
add (vec5 a b c d e) (vec5 f g h i j) =
  vec5 (A.add3 a f) (A.add3 b g) (A.add3 c h)
       (A.add3 d i) (A.add3 e j)

scale : Trit → Vec5 → Vec5
scale k (vec5 a b c d e) =
  vec5 (A.mul3 k a) (A.mul3 k b) (A.mul3 k c)
       (A.mul3 k d) (A.mul3 k e)

sub : Vec5 → Vec5 → Vec5
sub x y = add x (scale neg y)

indicator : Pivot → Vec5
indicator p01 = vec5 zer zer pos pos pos
indicator p02 = vec5 zer pos zer pos pos
indicator p03 = vec5 zer pos pos zer pos
indicator p04 = vec5 zer pos pos pos zer
indicator p12 = vec5 pos zer zer pos pos
indicator p13 = vec5 pos zer pos zer pos
indicator p14 = vec5 pos zer pos pos zer
indicator p23 = vec5 pos pos zer zer pos
indicator p24 = vec5 pos pos zer pos zer
indicator p34 = vec5 pos pos pos zer zer

record Direction : Set where
  constructor direction
  field
    u v : Vec5

determinant : Direction → Pivot → Trit
determinant (direction u v) p =
  A.add3 (A.mul3 (at (first p) u) (at (second p) v))
    (inv (A.mul3 (at (second p) u) (at (first p) v)))

-- Nonzero determinant supplies actual rank-two independence.
record Mark (L : Direction) : Set where
  constructor mark
  field
    pivot : Pivot
    admissible : O.Nonzero (determinant L pivot)

-- Factor the existing formula without changing its coordinates or guard.
linear2 : Trit → Trit → Trit → Trit → Trit → Trit
linear2 d a b x y =
  A.mul3 d (A.add3 (A.mul3 a x) (inv (A.mul3 b y)))

coefficientA coefficientB : {L : Direction} → Mark L → Vec5 → Trit
coefficientA {direction u v} (mark p nz) x =
  linear2 (O.reciprocal (determinant (direction u v) p) nz)
    (at (second p) v) (at (first p) v) (at (first p) x) (at (second p) x)
coefficientB {direction u v} (mark p nz) x =
  linear2 (O.reciprocal (determinant (direction u v) p) nz)
    (at (first p) u) (at (second p) u) (at (second p) x) (at (first p) x)

project : {L : Direction} → Mark L → Vec5 → Vec5
project {direction u v} q x =
  sub x (add (scale (coefficientA q x) u) (scale (coefficientB q x) v))

w : {L : Direction} → Mark L → Vec5
w p = indicator (Mark.pivot p)

raw : {L : Direction} → Mark L → Vec5 → Trit → Vec5
raw q x n = project q (add x (scale n (w q)))

correction : {L : Direction} → Mark L → Mark L → Trit → Vec5
correction p q n = scale n (project q (sub (w p) (w q)))

actual : {L : Direction} → Mark L → Mark L → Vec5 → Trit → Vec5
actual p q x n = project q (add x (scale n (w p)))

record ProjectionLaws (L : Direction) : Set where
  field
    corrected : (p v : Mark L) (x : Vec5) (n : Trit) →
      add (raw v x n) (correction p v n) ≡ actual p v x n
    compose : (v q : Mark L) (x : Vec5) →
      project q (project v x) ≡ project q x

-- Anchor and winding are indexed separately from observed quotient values.
-- S.Context retains integer winding, history and independent Phase4.
record Local {L : Direction} (p v : Mark L) : Set where
  constructor local
  field
    rawOffset signedCorrection : Vec5
    residue : Trit
    context : S.Context

record Shared {L : Direction} (p q : Mark L) : Set where
  constructor shared
  field
    normalized : Vec5
    residue : Trit
    context : S.Context

-- Each local chart is incident to each quotient-normalized edge of the same
-- direction. This is a chart-overlap hypergraph, not spatial cube incidence.
data Incidence {L : Direction} (v q : Mark L) : Set where
  sameDirection : Incidence v q

restrict : {L : Direction} {p v q : Mark L} →
  Incidence v q → Local p v → Shared p q
restrict {q = q} sameDirection (local y r n k) =
  shared (project q (add y r)) n k

fabric : {L : Direction} → (p : Mark L) →
  F.TypedHyperfabric (Mark L) (Mark L)
fabric p = record
  { vertexStalk = Local p
  ; edgeStalk = Shared p
  ; incidence = Incidence
  ; restrict = restrict
  ; edgeProvenance = λ _ → "same direction, admissible pivot" ∷ []
  ; edgeSalience = λ _ → 9
  ; fabricLabel = "H07 full admissible affine chart family"
  }

section : {L : Direction} (laws : ProjectionLaws L) →
  (p : Mark L) → Vec5 → Trit → S.Context → F.GlobalSection (fabric p)
section laws p x n k = record
  { vertexValue = λ v → local (raw v x n) (correction p v n) n k
  ; edgeValue = λ q → shared (actual p q x n) n k
  ; compatible = λ { {vertex = v} {edge = q} sameDirection →
      cong (λ y → shared y n k)
        (trans (cong (project q) (ProjectionLaws.corrected laws p v x n))
               (ProjectionLaws.compose laws v q (add x (scale n (w p))))) }
  ; sectionReceipt = "signed local corrections retained, common quotient restriction"
  }

-- The original selected nonzero-correction specimen supplies the context
-- type. The complete finite audit verifies the projection laws on every
-- admissible chart, but does not supply a kernel proof of ProjectionLaws.
-- Full indexed residual ledger is checked externally; local stalks above
-- retain each correction rather than encoding it as a shared scalar.


-- Literal anchor-local rotateTriple on the three complement coordinates.
-- The target chart MARK moves with the ambient axes; pivot order can swap.
rotateVec : Pivot → Vec5 → Vec5
rotateVec p01 (vec5 x0 x1 x2 x3 x4) = vec5 x0 x1 x3 x4 x2
rotateVec p02 (vec5 x0 x1 x2 x3 x4) = vec5 x0 x3 x2 x4 x1
rotateVec p03 (vec5 x0 x1 x2 x3 x4) = vec5 x0 x2 x4 x3 x1
rotateVec p04 (vec5 x0 x1 x2 x3 x4) = vec5 x0 x2 x3 x1 x4
rotateVec p12 (vec5 x0 x1 x2 x3 x4) = vec5 x3 x1 x2 x4 x0
rotateVec p13 (vec5 x0 x1 x2 x3 x4) = vec5 x2 x1 x4 x3 x0
rotateVec p14 (vec5 x0 x1 x2 x3 x4) = vec5 x2 x1 x3 x0 x4
rotateVec p23 (vec5 x0 x1 x2 x3 x4) = vec5 x1 x4 x2 x3 x0
rotateVec p24 (vec5 x0 x1 x2 x3 x4) = vec5 x1 x3 x2 x0 x4
rotateVec p34 (vec5 x0 x1 x2 x3 x4) = vec5 x1 x2 x0 x3 x4

rotateDirection : Pivot → Direction → Direction
rotateDirection p (direction u v) = direction (rotateVec p u) (rotateVec p v)

rotatePivot : Pivot → Pivot → Pivot
rotatePivot p01 p01 = p01
rotatePivot p01 p02 = p04
rotatePivot p01 p03 = p02
rotatePivot p01 p04 = p03
rotatePivot p01 p12 = p14
rotatePivot p01 p13 = p12
rotatePivot p01 p14 = p13
rotatePivot p01 p23 = p24
rotatePivot p01 p24 = p34
rotatePivot p01 p34 = p23
rotatePivot p02 p01 = p04
rotatePivot p02 p02 = p02
rotatePivot p02 p03 = p01
rotatePivot p02 p04 = p03
rotatePivot p02 p12 = p24
rotatePivot p02 p13 = p14
rotatePivot p02 p14 = p34
rotatePivot p02 p23 = p12
rotatePivot p02 p24 = p23
rotatePivot p02 p34 = p13
rotatePivot p03 p01 = p04
rotatePivot p03 p02 = p01
rotatePivot p03 p03 = p03
rotatePivot p03 p04 = p02
rotatePivot p03 p12 = p14
rotatePivot p03 p13 = p34
rotatePivot p03 p14 = p24
rotatePivot p03 p23 = p13
rotatePivot p03 p24 = p12
rotatePivot p03 p34 = p23
rotatePivot p04 p01 = p03
rotatePivot p04 p02 = p01
rotatePivot p04 p03 = p02
rotatePivot p04 p04 = p04
rotatePivot p04 p12 = p13
rotatePivot p04 p13 = p23
rotatePivot p04 p14 = p34
rotatePivot p04 p23 = p12
rotatePivot p04 p24 = p14
rotatePivot p04 p34 = p24
rotatePivot p12 p01 = p14
rotatePivot p12 p02 = p24
rotatePivot p12 p03 = p04
rotatePivot p12 p04 = p34
rotatePivot p12 p12 = p12
rotatePivot p12 p13 = p01
rotatePivot p12 p14 = p13
rotatePivot p12 p23 = p02
rotatePivot p12 p24 = p23
rotatePivot p12 p34 = p03
rotatePivot p13 p01 = p14
rotatePivot p13 p02 = p04
rotatePivot p13 p03 = p34
rotatePivot p13 p04 = p24
rotatePivot p13 p12 = p01
rotatePivot p13 p13 = p13
rotatePivot p13 p14 = p12
rotatePivot p13 p23 = p03
rotatePivot p13 p24 = p02
rotatePivot p13 p34 = p23
rotatePivot p14 p01 = p13
rotatePivot p14 p02 = p03
rotatePivot p14 p03 = p23
rotatePivot p14 p04 = p34
rotatePivot p14 p12 = p01
rotatePivot p14 p13 = p12
rotatePivot p14 p14 = p14
rotatePivot p14 p23 = p02
rotatePivot p14 p24 = p04
rotatePivot p14 p34 = p24
rotatePivot p23 p01 = p04
rotatePivot p23 p02 = p24
rotatePivot p23 p03 = p34
rotatePivot p23 p04 = p14
rotatePivot p23 p12 = p02
rotatePivot p23 p13 = p03
rotatePivot p23 p14 = p01
rotatePivot p23 p23 = p23
rotatePivot p23 p24 = p12
rotatePivot p23 p34 = p13
rotatePivot p24 p01 = p03
rotatePivot p24 p02 = p23
rotatePivot p24 p03 = p13
rotatePivot p24 p04 = p34
rotatePivot p24 p12 = p02
rotatePivot p24 p13 = p01
rotatePivot p24 p14 = p04
rotatePivot p24 p23 = p12
rotatePivot p24 p24 = p24
rotatePivot p24 p34 = p14
rotatePivot p34 p01 = p02
rotatePivot p34 p02 = p12
rotatePivot p34 p03 = p23
rotatePivot p34 p04 = p24
rotatePivot p34 p12 = p01
rotatePivot p34 p13 = p03
rotatePivot p34 p14 = p04
rotatePivot p34 p23 = p13
rotatePivot p34 p24 = p14
rotatePivot p34 p34 = p34

swapsPivotOrder : Pivot → Pivot → Bool
swapsPivotOrder p01 p01 = false
swapsPivotOrder p01 p02 = false
swapsPivotOrder p01 p03 = false
swapsPivotOrder p01 p04 = false
swapsPivotOrder p01 p12 = false
swapsPivotOrder p01 p13 = false
swapsPivotOrder p01 p14 = false
swapsPivotOrder p01 p23 = true
swapsPivotOrder p01 p24 = true
swapsPivotOrder p01 p34 = false
swapsPivotOrder p02 p01 = false
swapsPivotOrder p02 p02 = false
swapsPivotOrder p02 p03 = false
swapsPivotOrder p02 p04 = false
swapsPivotOrder p02 p12 = true
swapsPivotOrder p02 p13 = true
swapsPivotOrder p02 p14 = true
swapsPivotOrder p02 p23 = true
swapsPivotOrder p02 p24 = false
swapsPivotOrder p02 p34 = false
swapsPivotOrder p03 p01 = false
swapsPivotOrder p03 p02 = false
swapsPivotOrder p03 p03 = false
swapsPivotOrder p03 p04 = false
swapsPivotOrder p03 p12 = true
swapsPivotOrder p03 p13 = true
swapsPivotOrder p03 p14 = true
swapsPivotOrder p03 p23 = false
swapsPivotOrder p03 p24 = false
swapsPivotOrder p03 p34 = true
swapsPivotOrder p04 p01 = false
swapsPivotOrder p04 p02 = false
swapsPivotOrder p04 p03 = false
swapsPivotOrder p04 p04 = false
swapsPivotOrder p04 p12 = true
swapsPivotOrder p04 p13 = true
swapsPivotOrder p04 p14 = false
swapsPivotOrder p04 p23 = false
swapsPivotOrder p04 p24 = false
swapsPivotOrder p04 p34 = false
swapsPivotOrder p12 p01 = true
swapsPivotOrder p12 p02 = true
swapsPivotOrder p12 p03 = true
swapsPivotOrder p12 p04 = true
swapsPivotOrder p12 p12 = false
swapsPivotOrder p12 p13 = true
swapsPivotOrder p12 p14 = false
swapsPivotOrder p12 p23 = true
swapsPivotOrder p12 p24 = false
swapsPivotOrder p12 p34 = false
swapsPivotOrder p13 p01 = true
swapsPivotOrder p13 p02 = true
swapsPivotOrder p13 p03 = true
swapsPivotOrder p13 p04 = true
swapsPivotOrder p13 p12 = true
swapsPivotOrder p13 p13 = false
swapsPivotOrder p13 p14 = false
swapsPivotOrder p13 p23 = false
swapsPivotOrder p13 p24 = false
swapsPivotOrder p13 p34 = true
swapsPivotOrder p14 p01 = true
swapsPivotOrder p14 p02 = true
swapsPivotOrder p14 p03 = true
swapsPivotOrder p14 p04 = false
swapsPivotOrder p14 p12 = true
swapsPivotOrder p14 p13 = false
swapsPivotOrder p14 p14 = false
swapsPivotOrder p14 p23 = false
swapsPivotOrder p14 p24 = false
swapsPivotOrder p14 p34 = false
swapsPivotOrder p23 p01 = true
swapsPivotOrder p23 p02 = true
swapsPivotOrder p23 p03 = true
swapsPivotOrder p23 p04 = true
swapsPivotOrder p23 p12 = false
swapsPivotOrder p23 p13 = false
swapsPivotOrder p23 p14 = false
swapsPivotOrder p23 p23 = false
swapsPivotOrder p23 p24 = true
swapsPivotOrder p23 p34 = true
swapsPivotOrder p24 p01 = true
swapsPivotOrder p24 p02 = true
swapsPivotOrder p24 p03 = true
swapsPivotOrder p24 p04 = false
swapsPivotOrder p24 p12 = false
swapsPivotOrder p24 p13 = false
swapsPivotOrder p24 p14 = false
swapsPivotOrder p24 p23 = true
swapsPivotOrder p24 p24 = false
swapsPivotOrder p24 p34 = false
swapsPivotOrder p34 p01 = true
swapsPivotOrder p34 p02 = true
swapsPivotOrder p34 p03 = false
swapsPivotOrder p34 p04 = false
swapsPivotOrder p34 p12 = false
swapsPivotOrder p34 p13 = false
swapsPivotOrder p34 p14 = false
swapsPivotOrder p34 p23 = false
swapsPivotOrder p34 p24 = false
swapsPivotOrder p34 p34 = false

signedDet : Bool → Trit → Trit
signedDet false t = t
signedDet true t = inv t

detSwap : (a b c d : Trit) →
  A.add3 (A.mul3 b c) (inv (A.mul3 a d)) ≡
  inv (A.add3 (A.mul3 a d) (inv (A.mul3 b c)))
detSwap neg neg neg neg = refl
detSwap neg neg neg zer = refl
detSwap neg neg neg pos = refl
detSwap neg neg zer neg = refl
detSwap neg neg zer zer = refl
detSwap neg neg zer pos = refl
detSwap neg neg pos neg = refl
detSwap neg neg pos zer = refl
detSwap neg neg pos pos = refl
detSwap neg zer neg neg = refl
detSwap neg zer neg zer = refl
detSwap neg zer neg pos = refl
detSwap neg zer zer neg = refl
detSwap neg zer zer zer = refl
detSwap neg zer zer pos = refl
detSwap neg zer pos neg = refl
detSwap neg zer pos zer = refl
detSwap neg zer pos pos = refl
detSwap neg pos neg neg = refl
detSwap neg pos neg zer = refl
detSwap neg pos neg pos = refl
detSwap neg pos zer neg = refl
detSwap neg pos zer zer = refl
detSwap neg pos zer pos = refl
detSwap neg pos pos neg = refl
detSwap neg pos pos zer = refl
detSwap neg pos pos pos = refl
detSwap zer neg neg neg = refl
detSwap zer neg neg zer = refl
detSwap zer neg neg pos = refl
detSwap zer neg zer neg = refl
detSwap zer neg zer zer = refl
detSwap zer neg zer pos = refl
detSwap zer neg pos neg = refl
detSwap zer neg pos zer = refl
detSwap zer neg pos pos = refl
detSwap zer zer neg neg = refl
detSwap zer zer neg zer = refl
detSwap zer zer neg pos = refl
detSwap zer zer zer neg = refl
detSwap zer zer zer zer = refl
detSwap zer zer zer pos = refl
detSwap zer zer pos neg = refl
detSwap zer zer pos zer = refl
detSwap zer zer pos pos = refl
detSwap zer pos neg neg = refl
detSwap zer pos neg zer = refl
detSwap zer pos neg pos = refl
detSwap zer pos zer neg = refl
detSwap zer pos zer zer = refl
detSwap zer pos zer pos = refl
detSwap zer pos pos neg = refl
detSwap zer pos pos zer = refl
detSwap zer pos pos pos = refl
detSwap pos neg neg neg = refl
detSwap pos neg neg zer = refl
detSwap pos neg neg pos = refl
detSwap pos neg zer neg = refl
detSwap pos neg zer zer = refl
detSwap pos neg zer pos = refl
detSwap pos neg pos neg = refl
detSwap pos neg pos zer = refl
detSwap pos neg pos pos = refl
detSwap pos zer neg neg = refl
detSwap pos zer neg zer = refl
detSwap pos zer neg pos = refl
detSwap pos zer zer neg = refl
detSwap pos zer zer zer = refl
detSwap pos zer zer pos = refl
detSwap pos zer pos neg = refl
detSwap pos zer pos zer = refl
detSwap pos zer pos pos = refl
detSwap pos pos neg neg = refl
detSwap pos pos neg zer = refl
detSwap pos pos neg pos = refl
detSwap pos pos zer neg = refl
detSwap pos pos zer zer = refl
detSwap pos pos zer pos = refl
detSwap pos pos pos neg = refl
detSwap pos pos pos zer = refl
detSwap pos pos pos pos = refl

rotatedDet : (p q : Pivot) (L : Direction) →
  determinant (rotateDirection p L) (rotatePivot p q) ≡
  signedDet (swapsPivotOrder p q) (determinant L q)
rotatedDet p01 p01 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p01 p02 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p01 p03 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p01 p04 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p01 p12 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p01 p13 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p01 p14 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p01 p23 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u2 u3 v2 v3
rotatedDet p01 p24 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u2 u4 v2 v4
rotatedDet p01 p34 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p02 p01 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p02 p02 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p02 p03 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p02 p04 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p02 p12 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u1 u2 v1 v2
rotatedDet p02 p13 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u1 u3 v1 v3
rotatedDet p02 p14 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u1 u4 v1 v4
rotatedDet p02 p23 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u2 u3 v2 v3
rotatedDet p02 p24 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p02 p34 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p03 p01 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p03 p02 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p03 p03 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p03 p04 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p03 p12 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u1 u2 v1 v2
rotatedDet p03 p13 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u1 u3 v1 v3
rotatedDet p03 p14 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u1 u4 v1 v4
rotatedDet p03 p23 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p03 p24 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p03 p34 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u3 u4 v3 v4
rotatedDet p04 p01 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p04 p02 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p04 p03 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p04 p04 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p04 p12 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u1 u2 v1 v2
rotatedDet p04 p13 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u1 u3 v1 v3
rotatedDet p04 p14 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p04 p23 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p04 p24 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p04 p34 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p12 p01 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u1 v0 v1
rotatedDet p12 p02 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u2 v0 v2
rotatedDet p12 p03 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u3 v0 v3
rotatedDet p12 p04 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u4 v0 v4
rotatedDet p12 p12 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p12 p13 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u1 u3 v1 v3
rotatedDet p12 p14 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p12 p23 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u2 u3 v2 v3
rotatedDet p12 p24 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p12 p34 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p13 p01 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u1 v0 v1
rotatedDet p13 p02 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u2 v0 v2
rotatedDet p13 p03 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u3 v0 v3
rotatedDet p13 p04 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u4 v0 v4
rotatedDet p13 p12 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u1 u2 v1 v2
rotatedDet p13 p13 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p13 p14 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p13 p23 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p13 p24 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p13 p34 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u3 u4 v3 v4
rotatedDet p14 p01 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u1 v0 v1
rotatedDet p14 p02 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u2 v0 v2
rotatedDet p14 p03 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u3 v0 v3
rotatedDet p14 p04 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p14 p12 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u1 u2 v1 v2
rotatedDet p14 p13 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p14 p14 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p14 p23 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p14 p24 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p14 p34 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p23 p01 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u1 v0 v1
rotatedDet p23 p02 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u2 v0 v2
rotatedDet p23 p03 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u3 v0 v3
rotatedDet p23 p04 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u4 v0 v4
rotatedDet p23 p12 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p23 p13 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p23 p14 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p23 p23 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p23 p24 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u2 u4 v2 v4
rotatedDet p23 p34 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u3 u4 v3 v4
rotatedDet p24 p01 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u1 v0 v1
rotatedDet p24 p02 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u2 v0 v2
rotatedDet p24 p03 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u3 v0 v3
rotatedDet p24 p04 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p24 p12 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p24 p13 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p24 p14 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p24 p23 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u2 u3 v2 v3
rotatedDet p24 p24 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p24 p34 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p34 p01 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u1 v0 v1
rotatedDet p34 p02 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = detSwap u0 u2 v0 v2
rotatedDet p34 p03 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p34 p04 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p34 p12 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p34 p13 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p34 p14 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p34 p23 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p34 p24 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl
rotatedDet p34 p34 (direction (vec5 u0 u1 u2 u3 u4) (vec5 v0 v1 v2 v3 v4)) = refl

signedNonzero : (s : Bool) {t : Trit} → O.Nonzero t → O.Nonzero (signedDet s t)
signedNonzero false nz = nz
signedNonzero true O.negative = O.positive
signedNonzero true O.positive = O.negative

rotateMark : (p : Pivot) {L : Direction} → Mark L → Mark (rotateDirection p L)
rotateMark p {L} (mark q nz) =
  mark (rotatePivot p q)
    (subst O.Nonzero (sym (rotatedDet p q L))
      (signedNonzero (swapsPivotOrder p q) nz))

-- Source-written 100 literal pivot cases + 81 ternary determinant sign
-- cases. This discharges the transported nonzero guard at source level,
-- distinct from full projection naturality and kernel acceptance.
