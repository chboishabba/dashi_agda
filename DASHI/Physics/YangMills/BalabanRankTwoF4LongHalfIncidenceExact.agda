module DASHI.Physics.YangMills.BalabanRankTwoF4LongHalfIncidenceExact where

-- A constructive refinement of Round56 rank-two cells into the standard
-- W(B4)-coordinate F4 long24 / half-root16 incidence geometry.
-- Source geometry/action: BalabanClayT4GeneratedBrillouinGridExact,
-- BalabanClayT4HypercubicOrbitGeometryExact and GeneratedActionExact.
--
-- Each original interval axis has a signed OUTER component and a
-- signed HALF-ROOT component, with compatibility on outer axes.
-- A rank-two cell determines a compatible long/half pair; conversely
-- that pair reconstructs its exact original interval labels.
-- This is NOT a folded E6/F4 Weyl-action recognition or physical source.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Orbit
import DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact as Action

data SignedOuter : Set where
  inner outerNegative outerPositive : SignedOuter

data HalfSign : Set where
  negative positive : HalfSign

data Compatible : SignedOuter → HalfSign → Set where
  negativeInnerCompatible : Compatible inner negative
  positiveInnerCompatible : Compatible inner positive
  negativeOuterCompatible : Compatible outerNegative negative
  positiveOuterCompatible : Compatible outerPositive positive

record AxisIncidence : Set where
  constructor axisIncidence
  field
    support : SignedOuter
    halfSign : HalfSign
    compatibility : Compatible support halfSign
open AxisIncidence public

axisFromInterval : Grid.IntervalCell → AxisIncidence
axisFromInterval Grid.negativeOuter =
  axisIncidence outerNegative negative negativeOuterCompatible
axisFromInterval Grid.negativeInner =
  axisIncidence inner negative negativeInnerCompatible
axisFromInterval Grid.positiveInner =
  axisIncidence inner positive positiveInnerCompatible
axisFromInterval Grid.positiveOuter =
  axisIncidence outerPositive positive positiveOuterCompatible

intervalFromAxis : AxisIncidence → Grid.IntervalCell
intervalFromAxis (axisIncidence inner negative negativeInnerCompatible) =
  Grid.negativeInner
intervalFromAxis (axisIncidence inner positive positiveInnerCompatible) =
  Grid.positiveInner
intervalFromAxis (axisIncidence outerNegative negative negativeOuterCompatible) =
  Grid.negativeOuter
intervalFromAxis (axisIncidence outerPositive positive positiveOuterCompatible) =
  Grid.positiveOuter

intervalAxisRoundTrip : (c : Grid.IntervalCell) →
  intervalFromAxis (axisFromInterval c) ≡ c
intervalAxisRoundTrip Grid.negativeOuter = refl
intervalAxisRoundTrip Grid.negativeInner = refl
intervalAxisRoundTrip Grid.positiveInner = refl
intervalAxisRoundTrip Grid.positiveOuter = refl

axisIntervalRoundTrip : (a : AxisIncidence) →
  axisFromInterval (intervalFromAxis a) ≡ a
axisIntervalRoundTrip (axisIncidence inner negative negativeInnerCompatible) = refl
axisIntervalRoundTrip (axisIncidence inner positive positiveInnerCompatible) = refl
axisIntervalRoundTrip (axisIncidence outerNegative negative negativeOuterCompatible) = refl
axisIntervalRoundTrip (axisIncidence outerPositive positive positiveOuterCompatible) = refl

record Incidence4 : Set where
  constructor incidence4
  field
    a0 a1 a2 a3 : AxisIncidence
open Incidence4 public

toIncidence : Grid.GridCell4 → Incidence4
toIncidence (Grid.gridCell4 a b c d) =
  incidence4 (axisFromInterval a) (axisFromInterval b)
             (axisFromInterval c) (axisFromInterval d)

fromIncidence : Incidence4 → Grid.GridCell4
fromIncidence (incidence4 a b c d) =
  Grid.gridCell4 (intervalFromAxis a) (intervalFromAxis b)
                 (intervalFromAxis c) (intervalFromAxis d)

sourceReconstruction : (c : Grid.GridCell4) →
  fromIncidence (toIncidence c) ≡ c
sourceReconstruction (Grid.gridCell4 a b c d)
  rewrite intervalAxisRoundTrip a | intervalAxisRoundTrip b
        | intervalAxisRoundTrip c | intervalAxisRoundTrip d = refl

incidenceReconstruction : (p : Incidence4) →
  toIncidence (fromIncidence p) ≡ p
incidenceReconstruction (incidence4 a b c d)
  rewrite axisIntervalRoundTrip a | axisIntervalRoundTrip b
        | axisIntervalRoundTrip c | axisIntervalRoundTrip d = refl

-- The F4 long roots in doubled coordinates have exactly two entries
-- +/-2; the 16 doubled F4 half roots have every coordinate +/-1.
-- SignedOuter is 0 / +/-2, HalfSign is +/-1.
record Long4 : Set where
  constructor long4
  field
    l0 l1 l2 l3 : SignedOuter
open Long4 public

record Half4 : Set where
  constructor half4
  field
    h0 h1 h2 h3 : HalfSign
open Half4 public

longProjection : Incidence4 → Long4
longProjection (incidence4 a b c d) =
  long4 (support a) (support b) (support c) (support d)

halfProjection : Incidence4 → Half4
halfProjection (incidence4 a b c d) =
  half4 (halfSign a) (halfSign b) (halfSign c) (halfSign d)

weight : SignedOuter → Nat
weight inner = zero
weight outerNegative = suc zero
weight outerPositive = suc zero

longWeight : Long4 → Nat
longWeight v =
  weight (l0 v) + weight (l1 v) +
  weight (l2 v) + weight (l3 v)

axisWeightMatches : (c : Grid.IntervalCell) →
  weight (support (axisFromInterval c)) ≡ Orbit.outerWeight c
axisWeightMatches Grid.negativeOuter = refl
axisWeightMatches Grid.negativeInner = refl
axisWeightMatches Grid.positiveInner = refl
axisWeightMatches Grid.positiveOuter = refl

longWeightMatchesOriginal : (c : Grid.GridCell4) →
  longWeight (longProjection (toIncidence c)) ≡ Orbit.outerCount c
longWeightMatchesOriginal (Grid.gridCell4 a b c d)
  rewrite axisWeightMatches a | axisWeightMatches b
        | axisWeightMatches c | axisWeightMatches d = refl

record RankTwoCell : Set where
  constructor rankTwoCell
  field
    originalCell : Grid.GridCell4
    originalTwo : Orbit.outerCount originalCell ≡ 2
open RankTwoCell public

record F4LongHalfIncidence96 : Set where
  constructor f4LongHalfIncidence96
  field
    compatiblePair : Incidence4
    longHasTwo : longWeight (longProjection compatiblePair) ≡ 2
open F4LongHalfIncidence96 public

encodeRankTwo : RankTwoCell → F4LongHalfIncidence96
encodeRankTwo (rankTwoCell c two) =
  f4LongHalfIncidence96 (toIncidence c)
    (trans (longWeightMatchesOriginal c) two)

decodeRankTwo : F4LongHalfIncidence96 → RankTwoCell
decodeRankTwo (f4LongHalfIncidence96 p two) =
  rankTwoCell (fromIncidence p)
    (trans (sym (longWeightMatchesOriginal (fromIncidence p)))
      (trans
        (cong (λ q → longWeight (longProjection q))
          (incidenceReconstruction p))
        two))

sourceRankTwoReconstruction : (c : RankTwoCell) →
  originalCell (decodeRankTwo (encodeRankTwo c)) ≡ originalCell c
sourceRankTwoReconstruction (rankTwoCell c _) = sourceReconstruction c

incidenceRankTwoReconstruction : (p : F4LongHalfIncidence96) →
  compatiblePair (encodeRankTwo (decodeRankTwo p)) ≡ compatiblePair p
incidenceRankTwoReconstruction (f4LongHalfIncidence96 p _) =
  incidenceReconstruction p

rankTwoEncodingInjectiveOnOriginalCells :
  (a b : RankTwoCell) →
  compatiblePair (encodeRankTwo a) ≡ compatiblePair (encodeRankTwo b) →
  originalCell a ≡ originalCell b
rankTwoEncodingInjectiveOnOriginalCells a b equal =
  trans
    (sym (sourceRankTwoReconstruction a))
    (trans (cong fromIncidence equal)
      (sourceRankTwoReconstruction b))

-- Selected source B4 action restricts to rank two by the original
-- outerCountGeneratorInvariant theorem. The action on incidence is
-- induced via an *already proved* reconstruction, not asserted to be
-- the separately owned E6-folded W(F4) action on 48 roots.
sourceRankTwoAct :
  Action.HypercubicGenerator → RankTwoCell → RankTwoCell
sourceRankTwoAct g (rankTwoCell c two) =
  rankTwoCell (Action.act g c)
    (trans (Action.outerCountGeneratorInvariant g c) two)

incidenceAct :
  Action.HypercubicGenerator →
  F4LongHalfIncidence96 → F4LongHalfIncidence96
incidenceAct g p = encodeRankTwo (sourceRankTwoAct g (decodeRankTwo p))

incidenceActionEquivariant :
  (g : Action.HypercubicGenerator) (c : RankTwoCell) →
  compatiblePair (encodeRankTwo (sourceRankTwoAct g c)) ≡
  compatiblePair (incidenceAct g (encodeRankTwo c))
incidenceActionEquivariant g c =
  cong (λ cell → toIncidence (Action.act g cell))
    (sym (sourceRankTwoReconstruction c))

-- Fully separate target action compatibility for an INDEPENDENT F4
-- source remains open; the finite enumerator checks the standard
-- signed-coordinate action on 24 long and 16 half roots.
