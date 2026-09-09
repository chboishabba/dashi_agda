module DASHI.Moonshine.JInvariantOrderThreeVisibleScaleUniquenessBidiExact where

------------------------------------------------------------------------
-- VISIBLE ORDER-THREE SEAM SCALE UNIQUENESS, k = 0 .. 7
--
-- The current source-aligned rendered-beam programme already isolates the
-- finite candidate family k=0..7.  Its exact orbit scales are
--
--   1, 3, 7, 13, 21, 31, 43, 57.
--
-- This owner proves that scale is injective on that actual finite candidate
-- fibre.  Therefore a calibrated rendered/analytic box that determines one of
-- these exact scales does not need to carry a separate uniqueness authority.
-- No claim is made here about a general all-Nat monotonicity theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.JInvariantOrderThreeOrbitBalancedTernaryBidiExact as Orbit
import DASHI.Moonshine.JInvariantOrderThreeSeamScaleRecognitionBidiExact as Scale

------------------------------------------------------------------------
-- 1. Finite visible candidate fibre.
------------------------------------------------------------------------

data VisibleEightIndex : Set where
  visible0 visible1 visible2 visible3 : VisibleEightIndex
  visible4 visible5 visible6 visible7 : VisibleEightIndex

visibleIndex : VisibleEightIndex → Nat
visibleIndex visible0 = 0
visibleIndex visible1 = 1
visibleIndex visible2 = 2
visibleIndex visible3 = 3
visibleIndex visible4 = 4
visibleIndex visible5 = 5
visibleIndex visible6 = 6
visibleIndex visible7 = 7

visibleScale : VisibleEightIndex → Nat
visibleScale i = Scale.seamScale (visibleIndex i)

visible0Scale : visibleScale visible0 ≡ 1
visible0Scale = refl

visible1Scale : visibleScale visible1 ≡ 3
visible1Scale = refl

visible2Scale : visibleScale visible2 ≡ 7
visible2Scale = refl

visible3Scale : visibleScale visible3 ≡ 13
visible3Scale = refl

visible4Scale : visibleScale visible4 ≡ 21
visible4Scale = refl

visible5Scale : visibleScale visible5 ≡ 31
visible5Scale = refl

visible6Scale : visibleScale visible6 ≡ 43
visible6Scale = refl

visible7Scale : visibleScale visible7 ≡ 57
visible7Scale = refl

------------------------------------------------------------------------
-- 2. Exact finite injectivity.
------------------------------------------------------------------------

visibleScaleInjective :
  (left right : VisibleEightIndex) →
  visibleScale left ≡ visibleScale right →
  left ≡ right
visibleScaleInjective visible0 visible0 refl = refl
visibleScaleInjective visible0 visible1 ()
visibleScaleInjective visible0 visible2 ()
visibleScaleInjective visible0 visible3 ()
visibleScaleInjective visible0 visible4 ()
visibleScaleInjective visible0 visible5 ()
visibleScaleInjective visible0 visible6 ()
visibleScaleInjective visible0 visible7 ()
visibleScaleInjective visible1 visible0 ()
visibleScaleInjective visible1 visible1 refl = refl
visibleScaleInjective visible1 visible2 ()
visibleScaleInjective visible1 visible3 ()
visibleScaleInjective visible1 visible4 ()
visibleScaleInjective visible1 visible5 ()
visibleScaleInjective visible1 visible6 ()
visibleScaleInjective visible1 visible7 ()
visibleScaleInjective visible2 visible0 ()
visibleScaleInjective visible2 visible1 ()
visibleScaleInjective visible2 visible2 refl = refl
visibleScaleInjective visible2 visible3 ()
visibleScaleInjective visible2 visible4 ()
visibleScaleInjective visible2 visible5 ()
visibleScaleInjective visible2 visible6 ()
visibleScaleInjective visible2 visible7 ()
visibleScaleInjective visible3 visible0 ()
visibleScaleInjective visible3 visible1 ()
visibleScaleInjective visible3 visible2 ()
visibleScaleInjective visible3 visible3 refl = refl
visibleScaleInjective visible3 visible4 ()
visibleScaleInjective visible3 visible5 ()
visibleScaleInjective visible3 visible6 ()
visibleScaleInjective visible3 visible7 ()
visibleScaleInjective visible4 visible0 ()
visibleScaleInjective visible4 visible1 ()
visibleScaleInjective visible4 visible2 ()
visibleScaleInjective visible4 visible3 ()
visibleScaleInjective visible4 visible4 refl = refl
visibleScaleInjective visible4 visible5 ()
visibleScaleInjective visible4 visible6 ()
visibleScaleInjective visible4 visible7 ()
visibleScaleInjective visible5 visible0 ()
visibleScaleInjective visible5 visible1 ()
visibleScaleInjective visible5 visible2 ()
visibleScaleInjective visible5 visible3 ()
visibleScaleInjective visible5 visible4 ()
visibleScaleInjective visible5 visible5 refl = refl
visibleScaleInjective visible5 visible6 ()
visibleScaleInjective visible5 visible7 ()
visibleScaleInjective visible6 visible0 ()
visibleScaleInjective visible6 visible1 ()
visibleScaleInjective visible6 visible2 ()
visibleScaleInjective visible6 visible3 ()
visibleScaleInjective visible6 visible4 ()
visibleScaleInjective visible6 visible5 ()
visibleScaleInjective visible6 visible6 refl = refl
visibleScaleInjective visible6 visible7 ()
visibleScaleInjective visible7 visible0 ()
visibleScaleInjective visible7 visible1 ()
visibleScaleInjective visible7 visible2 ()
visibleScaleInjective visible7 visible3 ()
visibleScaleInjective visible7 visible4 ()
visibleScaleInjective visible7 visible5 ()
visibleScaleInjective visible7 visible6 ()
visibleScaleInjective visible7 visible7 refl = refl

------------------------------------------------------------------------
-- 3. BIDI recognition receipt.
------------------------------------------------------------------------

record VisibleScaleRecognition : Set where
  constructor visible-scale-recognition
  field
    candidate : VisibleEightIndex
    measuredScale : Nat
    scaleMatchesCandidate : measuredScale ≡ visibleScale candidate

open VisibleScaleRecognition public

sameMeasuredVisibleScaleForcesSameCandidate :
  (left right : VisibleScaleRecognition) →
  measuredScale left ≡ measuredScale right →
  candidate left ≡ candidate right
sameMeasuredVisibleScaleForcesSameCandidate left right same =
  visibleScaleInjective
    (candidate left)
    (candidate right)
    (trans
      (sym (scaleMatchesCandidate left))
      (trans same (scaleMatchesCandidate right)))

------------------------------------------------------------------------
-- 4. Frontier.
------------------------------------------------------------------------

record VisibleScaleUniquenessFrontier : Set where
  constructor visible-scale-uniqueness-frontier
  field
    visibleEightCandidateFibreExact : Bool
    exactScaleValuesComputed : Bool
    scaleInjectiveOnVisibleEight : Bool
    calibratedPixelBoxDeterminesExactVisibleScale : Bool
    generalNatScaleMonotonicityNeededForCurrentEight : Bool

canonicalVisibleScaleUniquenessFrontier : VisibleScaleUniquenessFrontier
canonicalVisibleScaleUniquenessFrontier =
  visible-scale-uniqueness-frontier
    true true true false false
