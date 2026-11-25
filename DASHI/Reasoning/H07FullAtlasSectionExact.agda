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

project : {L : Direction} → Mark L → Vec5 → Vec5
project {direction u v} (mark p nz) x =
  sub x (add (scale alpha u) (scale beta v))
  where
    d : Trit
    d = O.reciprocal (determinant (direction u v) p) nz

    alpha : Trit
    alpha = A.mul3 d
      (A.add3 (A.mul3 (at (second p) v) (at (first p) x))
        (inv (A.mul3 (at (first p) v) (at (second p) x))))

    beta : Trit
    beta = A.mul3 d
      (A.add3 (A.mul3 (at (first p) u) (at (second p) x))
        (inv (A.mul3 (at (second p) u) (at (first p) x))))

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
