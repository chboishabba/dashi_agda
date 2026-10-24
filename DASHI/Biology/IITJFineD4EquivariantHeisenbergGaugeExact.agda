module DASHI.Biology.IITJFineD4EquivariantHeisenbergGaugeExact where

-- New equivariant JFine decomposition. Reuses the original source-typed
-- relativeGauge/S3/D4 operators of PR #1148; no parallel Heisenberg group.
-- Source nine-site edge order N E S W, corner order NW NE SW SE.
-- Over F3, 1/2 = 2 = -1.  The opposite-edge half-differences are the
-- D4-stable 2D multiplicity label; half-sums and corners give a stable X6.
-- This does not identify the resulting normalizer with Monster N(3B).

open import DASHI.Core.Prelude
import Base369 as Base
import DASHI.Biology.IITJFineFourOneFourS3ZetaGaugeExact as Gauge
import DASHI.Moonshine.OggSSPP2F4RecenteredTriXorS3Exact as F3

add : Base.TriTruth → Base.TriTruth → Base.TriTruth
add = F3.centerAdd

neg : Base.TriTruth → Base.TriTruth
neg = F3.centerNeg

-- Opposite-site half sum/difference, using inv(2) = -1 in F3.
halfSum : Base.TriTruth → Base.TriTruth → Base.TriTruth
halfSum a b = neg (add a b)

halfDiff : Base.TriTruth → Base.TriTruth → Base.TriTruth
halfDiff a b = neg (add a (neg b))

restoreFirst : Base.TriTruth → Base.TriTruth → Base.TriTruth
restoreFirst x a = add x a

restoreSecond : Base.TriTruth → Base.TriTruth → Base.TriTruth
restoreSecond x a = add x (neg a)

-- All pair identities are exhaustive at the base F3 type, not postulates.
sumAfterRestore : ∀ x a →
  halfSum (restoreFirst x a) (restoreSecond x a) ≡ x
sumAfterRestore Base.tri-low Base.tri-low = refl
sumAfterRestore Base.tri-low Base.tri-mid = refl
sumAfterRestore Base.tri-low Base.tri-high = refl
sumAfterRestore Base.tri-mid Base.tri-low = refl
sumAfterRestore Base.tri-mid Base.tri-mid = refl
sumAfterRestore Base.tri-mid Base.tri-high = refl
sumAfterRestore Base.tri-high Base.tri-low = refl
sumAfterRestore Base.tri-high Base.tri-mid = refl
sumAfterRestore Base.tri-high Base.tri-high = refl

diffAfterRestore : ∀ x a →
  halfDiff (restoreFirst x a) (restoreSecond x a) ≡ a
diffAfterRestore Base.tri-low Base.tri-low = refl
diffAfterRestore Base.tri-low Base.tri-mid = refl
diffAfterRestore Base.tri-low Base.tri-high = refl
diffAfterRestore Base.tri-mid Base.tri-low = refl
diffAfterRestore Base.tri-mid Base.tri-mid = refl
diffAfterRestore Base.tri-mid Base.tri-high = refl
diffAfterRestore Base.tri-high Base.tri-low = refl
diffAfterRestore Base.tri-high Base.tri-mid = refl
diffAfterRestore Base.tri-high Base.tri-high = refl

firstAfterSplit : ∀ n s →
  restoreFirst (halfSum n s) (halfDiff n s) ≡ n
firstAfterSplit Base.tri-low Base.tri-low = refl
firstAfterSplit Base.tri-low Base.tri-mid = refl
firstAfterSplit Base.tri-low Base.tri-high = refl
firstAfterSplit Base.tri-mid Base.tri-low = refl
firstAfterSplit Base.tri-mid Base.tri-mid = refl
firstAfterSplit Base.tri-mid Base.tri-high = refl
firstAfterSplit Base.tri-high Base.tri-low = refl
firstAfterSplit Base.tri-high Base.tri-mid = refl
firstAfterSplit Base.tri-high Base.tri-high = refl

secondAfterSplit : ∀ n s →
  restoreSecond (halfSum n s) (halfDiff n s) ≡ s
secondAfterSplit Base.tri-low Base.tri-low = refl
secondAfterSplit Base.tri-low Base.tri-mid = refl
secondAfterSplit Base.tri-low Base.tri-high = refl
secondAfterSplit Base.tri-mid Base.tri-low = refl
secondAfterSplit Base.tri-mid Base.tri-mid = refl
secondAfterSplit Base.tri-mid Base.tri-high = refl
secondAfterSplit Base.tri-high Base.tri-low = refl
secondAfterSplit Base.tri-high Base.tri-mid = refl
secondAfterSplit Base.tri-high Base.tri-high = refl

halfSumSym : ∀ a b → halfSum b a ≡ halfSum a b
halfSumSym Base.tri-low Base.tri-low = refl
halfSumSym Base.tri-low Base.tri-mid = refl
halfSumSym Base.tri-low Base.tri-high = refl
halfSumSym Base.tri-mid Base.tri-low = refl
halfSumSym Base.tri-mid Base.tri-mid = refl
halfSumSym Base.tri-mid Base.tri-high = refl
halfSumSym Base.tri-high Base.tri-low = refl
halfSumSym Base.tri-high Base.tri-mid = refl
halfSumSym Base.tri-high Base.tri-high = refl

halfDiffReverse : ∀ a b →
  halfDiff b a ≡ neg (halfDiff a b)
halfDiffReverse Base.tri-low Base.tri-low = refl
halfDiffReverse Base.tri-low Base.tri-mid = refl
halfDiffReverse Base.tri-low Base.tri-high = refl
halfDiffReverse Base.tri-mid Base.tri-low = refl
halfDiffReverse Base.tri-mid Base.tri-mid = refl
halfDiffReverse Base.tri-mid Base.tri-high = refl
halfDiffReverse Base.tri-high Base.tri-low = refl
halfDiffReverse Base.tri-high Base.tri-mid = refl
halfDiffReverse Base.tri-high Base.tri-high = refl

record D4Chart : Set where
  constructor d4Chart
  field
    reference labelNS labelEW fibreNS fibreEW : Base.TriTruth
    corners : Gauge.FourTrit
open D4Chart public

toChart : Gauge.FourOneFour → D4Chart
toChart (Gauge.fourOneFour c (Gauge.fourTrit n e s w) corners) =
  d4Chart c (halfDiff n s) (halfDiff e w)
    (halfSum n s) (halfSum e w) corners

fromChart : D4Chart → Gauge.FourOneFour
fromChart (d4Chart c a b x y corners) =
  Gauge.fourOneFour c
    (Gauge.fourTrit (restoreFirst x a) (restoreFirst y b)
                    (restoreSecond x a) (restoreSecond y b))
    corners

chartRoundTrip : ∀ chart → toChart (fromChart chart) ≡ chart
chartRoundTrip (d4Chart c a b x y corners)
  rewrite diffAfterRestore x a | diffAfterRestore y b
        | sumAfterRestore x a | sumAfterRestore y b = refl

sheetRoundTrip : ∀ sheet → fromChart (toChart sheet) ≡ sheet
sheetRoundTrip (Gauge.fourOneFour c (Gauge.fourTrit n e s w) corners)
  rewrite firstAfterSplit n s | firstAfterSplit e w
        | secondAfterSplit n s | secondAfterSplit e w = refl

-- D4 acts on actual centre-relative source coordinates (not just counts).
quarterRelative : Gauge.FourOneFour → Gauge.FourOneFour
quarterRelative
  (Gauge.fourOneFour c (Gauge.fourTrit n e s w)
    (Gauge.fourTrit nw ne sw se)) =
  Gauge.fourOneFour c (Gauge.fourTrit w n e s)
    (Gauge.fourTrit sw nw se ne)

mirrorRelative : Gauge.FourOneFour → Gauge.FourOneFour
mirrorRelative
  (Gauge.fourOneFour c (Gauge.fourTrit n e s w)
    (Gauge.fourTrit nw ne sw se)) =
  Gauge.fourOneFour c (Gauge.fourTrit n w s e)
    (Gauge.fourTrit ne nw se sw)

quarterChart : D4Chart → D4Chart
quarterChart
  (d4Chart c a b x y (Gauge.fourTrit nw ne sw se)) =
  d4Chart c (neg b) a y x (Gauge.fourTrit sw nw se ne)

mirrorChart : D4Chart → D4Chart
mirrorChart
  (d4Chart c a b x y (Gauge.fourTrit nw ne sw se)) =
  d4Chart c a (neg b) x y (Gauge.fourTrit ne nw se sw)

quarterIntertwines : ∀ sheet →
  toChart (quarterRelative sheet) ≡ quarterChart (toChart sheet)
quarterIntertwines
  (Gauge.fourOneFour c (Gauge.fourTrit n e s w)
    (Gauge.fourTrit nw ne sw se))
  rewrite halfDiffReverse e w | halfSumSym e w = refl

mirrorIntertwines : ∀ sheet →
  toChart (mirrorRelative sheet) ≡ mirrorChart (toChart sheet)
mirrorIntertwines
  (Gauge.fourOneFour c (Gauge.fourTrit n e s w)
    (Gauge.fourTrit nw ne sw se))
  rewrite halfDiffReverse e w | halfSumSym e w = refl

-- Translational fibre is the two even opposite-edge modes + four corners;
-- the opposite-edge difference label never moves under E.
-- A D4 permutation of the six fibre sites induces the same permutation
-- on the dual modulation axes, hence preserves the canonical dot pairing.
-- Finite-Heisenberg multiplication, Stone--von Neumann and cocycle results
-- remain owned by DASHI.Moonshine.Monster3BFiniteHeisenberg* modules.

halfSumAndDifferenceDimension : 3 * 3 * 3 * 3 * 3 * 3 * 3 * 3 ≡ 6561
halfSumAndDifferenceDimension = refl

rechartedPointedDimensions : 10 * (3 * 3) * (3 * 3 * 3 * 3 * 3 * 3) * 3 ≡ 196830
rechartedPointedDimensions = refl
