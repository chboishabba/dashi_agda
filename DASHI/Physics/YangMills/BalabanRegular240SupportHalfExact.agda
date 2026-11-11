module DASHI.Physics.YangMills.BalabanRegular240SupportHalfExact where

-- Full regular 240-cell decomposition, using original grid and the
-- independently defined F4 half-root sign action from the rank-two
-- incidence owner. No exceptional E8/E6 same-object promotion.
-- Geometric equivalence: all 256 grid cells are 16 Boolean support
-- masks times 16 four-sign vectors. Removing zero support leaves 240.
-- All 7 original B4 generators commute with both projections.
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Action
import DASHI.Physics.YangMills.BalabanRankTwoF4LongHalfIncidenceExact as F4

record Mask4 : Set where
  constructor mask4
  field
    m0 m1 m2 m3 : Bool
open Mask4 public

record SupportHalf256 : Set where
  constructor supportHalf256
  field
    supportMask : Mask4
    halfRootSigns : F4.Half4
open SupportHalf256 public

axisMask : Grid.IntervalCell → Bool
axisMask = Orbit.outerFlag

axisSign : Grid.IntervalCell → F4.HalfSign
axisSign c = F4.halfSign (F4.axisFromInterval c)

encode256 : Grid.GridCell4 → SupportHalf256
encode256 (Grid.gridCell4 a b c d) = supportHalf256
  (mask4 (axisMask a) (axisMask b) (axisMask c) (axisMask d))
  (F4.half4 (axisSign a) (axisSign b) (axisSign c) (axisSign d))

decodeAxis : Bool → F4.HalfSign → Grid.IntervalCell
decodeAxis false F4.negative = Grid.negativeInner
decodeAxis false F4.positive = Grid.positiveInner
decodeAxis true F4.negative = Grid.negativeOuter
decodeAxis true F4.positive = Grid.positiveOuter

decode256 : SupportHalf256 → Grid.GridCell4
decode256 (supportHalf256 (mask4 a b c d) (F4.half4 x y z w)) =
  Grid.gridCell4 (decodeAxis a x) (decodeAxis b y)
                 (decodeAxis c z) (decodeAxis d w)

axisRoundTrip : (c : Grid.IntervalCell) →
  decodeAxis (axisMask c) (axisSign c) ≡ c
axisRoundTrip Grid.negativeOuter = refl
axisRoundTrip Grid.negativeInner = refl
axisRoundTrip Grid.positiveInner = refl
axisRoundTrip Grid.positiveOuter = refl

maskAxisRoundTrip : (b : Bool) (s : F4.HalfSign) →
  axisMask (decodeAxis b s) ≡ b
maskAxisRoundTrip false F4.negative = refl
maskAxisRoundTrip false F4.positive = refl
maskAxisRoundTrip true F4.negative = refl
maskAxisRoundTrip true F4.positive = refl

signAxisRoundTrip : (b : Bool) (s : F4.HalfSign) →
  axisSign (decodeAxis b s) ≡ s
signAxisRoundTrip false F4.negative = refl
signAxisRoundTrip false F4.positive = refl
signAxisRoundTrip true F4.negative = refl
signAxisRoundTrip true F4.positive = refl

source256RoundTrip : (c : Grid.GridCell4) →
  decode256 (encode256 c) ≡ c
source256RoundTrip (Grid.gridCell4 a b c d)
  rewrite axisRoundTrip a | axisRoundTrip b |
          axisRoundTrip c | axisRoundTrip d = refl

target256RoundTrip : (p : SupportHalf256) →
  encode256 (decode256 p) ≡ p
target256RoundTrip (supportHalf256 (mask4 a b c d) (F4.half4 x y z w))
  rewrite maskAxisRoundTrip a x | maskAxisRoundTrip b y |
          maskAxisRoundTrip c z | maskAxisRoundTrip d w |
          signAxisRoundTrip a x | signAxisRoundTrip b y |
          signAxisRoundTrip c z | signAxisRoundTrip d w = refl

maskWeight : Mask4 → Nat
maskWeight (mask4 a b c d) =
  Orbit.boolWeight a + Orbit.boolWeight b +
  Orbit.boolWeight c + Orbit.boolWeight d

sourceMaskWeight : (c : Grid.GridCell4) →
  maskWeight (supportMask (encode256 c)) ≡ Orbit.outerCount c
sourceMaskWeight (Grid.gridCell4 a b c d) = refl

record Regular240 : Set where
  constructor regular240
  field
    original : Grid.GridCell4
    degree : Nat
    nonzeroDegree : Orbit.outerCount original ≡ suc degree
open Regular240 public

record SupportHalf240 : Set where
  constructor supportHalf240
  field
    supportSigns : SupportHalf256
    supportDegree : Nat
    nonemptySupport : maskWeight (supportMask supportSigns) ≡ suc supportDegree
open SupportHalf240 public

encode240 : Regular240 → SupportHalf240
encode240 (regular240 c n nonzero) =
  supportHalf240 (encode256 c) n
    (trans (sourceMaskWeight c) nonzero)

decode240 : SupportHalf240 → Regular240
decode240 (supportHalf240 p n nonempty) =
  regular240 (decode256 p) n
    (trans
      (sym (sourceMaskWeight (decode256 p)))
      (trans (cong (λ q → maskWeight (supportMask q))
                   (target256RoundTrip p))
             nonempty))

regularOriginalRoundTrip : (c : Regular240) →
  original (decode240 (encode240 c)) ≡ original c
regularOriginalRoundTrip (regular240 c n proof) = source256RoundTrip c

regularPackedRoundTrip : (p : SupportHalf240) →
  supportSigns (encode240 (decode240 p)) ≡ supportSigns p
regularPackedRoundTrip (supportHalf240 p n proof) = target256RoundTrip p

-- Actions defined independently on the Boolean support and F4 half
-- sign roots. Flips preserve mask; adjacent swaps permute it.
actMask : Action.HypercubicGenerator → Mask4 → Mask4
actMask Action.flip0 m = m
actMask Action.flip1 m = m
actMask Action.flip2 m = m
actMask Action.flip3 m = m
actMask Action.swap01 (mask4 a b c d) = mask4 b a c d
actMask Action.swap12 (mask4 a b c d) = mask4 a c b d
actMask Action.swap23 (mask4 a b c d) = mask4 a b d c

maskFlipInvariant : (c : Grid.IntervalCell) →
  axisMask (Action.flipInterval c) ≡ axisMask c
maskFlipInvariant Grid.negativeOuter = refl
maskFlipInvariant Grid.negativeInner = refl
maskFlipInvariant Grid.positiveInner = refl
maskFlipInvariant Grid.positiveOuter = refl

maskProjectionEquivariant :
  (g : Action.HypercubicGenerator) (c : Grid.GridCell4) →
  supportMask (encode256 (Action.act g c)) ≡
  actMask g (supportMask (encode256 c))
maskProjectionEquivariant Action.flip0 (Grid.gridCell4 a b c d)
  rewrite maskFlipInvariant a = refl
maskProjectionEquivariant Action.flip1 (Grid.gridCell4 a b c d)
  rewrite maskFlipInvariant b = refl
maskProjectionEquivariant Action.flip2 (Grid.gridCell4 a b c d)
  rewrite maskFlipInvariant c = refl
maskProjectionEquivariant Action.flip3 (Grid.gridCell4 a b c d)
  rewrite maskFlipInvariant d = refl
maskProjectionEquivariant Action.swap01 (Grid.gridCell4 a b c d) = refl
maskProjectionEquivariant Action.swap12 (Grid.gridCell4 a b c d) = refl
maskProjectionEquivariant Action.swap23 (Grid.gridCell4 a b c d) = refl

halfProjectionEquivariant :
  (g : Action.HypercubicGenerator) (c : Grid.GridCell4) →
  halfRootSigns (encode256 (Action.act g c)) ≡
  F4.actHalf g (halfRootSigns (encode256 c))
halfProjectionEquivariant g c = F4.halfProjectionEquivariant g c

-- The Cartesian action is genuine and independent of the grid encoder.
actSupportHalf : Action.HypercubicGenerator →
  SupportHalf256 → SupportHalf256
actSupportHalf g (supportHalf256 mask signs) =
  supportHalf256 (actMask g mask) (F4.actHalf g signs)

full256Equivariant : (g : Action.HypercubicGenerator)
  (c : Grid.GridCell4) →
  encode256 (Action.act g c) ≡ actSupportHalf g (encode256 c)
full256Equivariant g c
  rewrite maskProjectionEquivariant g c |
          halfProjectionEquivariant g c = refl

-- The positive-support degree is preserved by the actual generated
-- source action. This is the complete four-rank regular 240 carrier.
actRegular : Action.HypercubicGenerator → Regular240 → Regular240
actRegular g (regular240 c n nonzero) =
  regular240 (Action.act g c) n
    (trans (Action.outerCountGeneratorInvariant g c) nonzero)

-- The full 240 support/sign target action is induced by the
-- independently defined Cartesian action and the positive degree
-- relation; the target carrier is not an arbitrary list of 240 indices.
actPackedRegular : Action.HypercubicGenerator →
  SupportHalf240 → SupportHalf240
actPackedRegular g p = encode240 (actRegular g (decode240 p))

regular240Equivariant : (g : Action.HypercubicGenerator)
  (c : Regular240) →
  supportSigns (encode240 (actRegular g c)) ≡
  supportSigns (actPackedRegular g (encode240 c))
regular240Equivariant g c =
  cong (λ x → encode256 (Action.act g x))
    (sym (regularOriginalRoundTrip c))

-- Pending: Agda proof that actPackedRegular equals the independent
-- Cartesian action at the proof-carrying subtype level (its underlying
-- projections commute already, by full256Equivariant).
-- The regular counting receipt is independent and already source-owned:
-- Grid.regularGridCellCount, Orbit.regularOrbitMultiplicitySum.

-- The underlying target Cartesian action is independent. At this level,
-- our proof-carrying action has exactly the same support/sign coordinates.
independentCartesianActionAgrees :
  (g : Action.HypercubicGenerator) (p : SupportHalf240) →
  supportSigns (actPackedRegular g p) ≡
  actSupportHalf g (supportSigns p)
independentCartesianActionAgrees g p =
  trans (full256Equivariant g (GridCell p))
    (cong (actSupportHalf g) (target256RoundTrip (supportSigns p)))
  where
    GridCell : SupportHalf240 → Grid.GridCell4
    GridCell q = GridCell′ (decode240 q)
      where
        GridCell′ : Regular240 → Grid.GridCell4
        GridCell′ = original

-- The 15 support masks, rather than all 16, supply the base space
-- after removing the all-inner 16-sign infrared fibre. Because the
-- source proof of positive outerCount was preserved, no hidden
-- IR admissibility claim is imported from a finite cardinality.
