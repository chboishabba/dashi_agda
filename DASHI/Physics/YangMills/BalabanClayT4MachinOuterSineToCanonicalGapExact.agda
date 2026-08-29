module DASHI.Physics.YangMills.BalabanClayT4MachinOuterSineToCanonicalGapExact where

------------------------------------------------------------------------
-- ROUND88: CANONICAL OUTER COORDINATE -> 7569/4096 WILSON COMPONENT GAP
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Errett Bishop and Douglas Bridges,
-- "Constructive Analysis", Springer, 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant", 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- MATHEMATICAL ROLE
--
-- Round57 already proves, for the ACTUAL Bishop sine power series and a
-- Machin-normalized outer angle t,
--
--      3/4 <= t <= 11/7
--        => (2 sin t)^2 >= 7569/4096.
--
-- Round86 makes the Wilson Fourier period definitionally the same Machin Bishop
-- pi.  Round88's regular-gap compiler proves that one outer component lower
-- bound propagates to the complete four-dimensional hat{k}^2.
--
-- This file supplies the missing theorem composition.  It does NOT ask for a
-- fresh trigonometric inequality.  The only same-object data are:
--
--   * an actual Machin-normalized outer coordinate for the selected box axis;
--   * the existing concrete radius-two sine-series inputs at that angle;
--   * identification of the canonical Wilson component with that exact
--     `(2 sin angle)^2` object.
--
-- Those data mechanically produce the fixed 7569/4096 component gap and then
-- the regular Wilson denominator gap.  Thus the remaining physical A2 seam is
-- coordinate/atom materialization, not interval or denominator analysis.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)

import Real as Bishop
import RealProperties as BishopP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4CanonicalBishopAtomEnvironmentExact as Canonical
import DASHI.Physics.YangMills.BalabanBishopSineTwoBallCubicLowerExact as Sine
import DASHI.Physics.YangMills.BalabanBishopOuterBrillouinSineGapExact as OuterSine
import DASHI.Physics.YangMills.BalabanBishopMachinNormalizedOuterMomentumExact as Machin
import DASHI.Physics.YangMills.BalabanClayT4BishopRegularHatMomentumGapExact as RegularGap

record MachinOuterSineCanonicalWeld
    (trig : Canonical.PhysicalTrigBoxData)
    (role : Eval.MomentumRole)
    (cell : Grid.GridCell4) : Set₁ where
  field
    elementary : Elementary.BishopElementaryPowerSeriesData

    axis0Coordinate : Grid.isInner (Grid.c0 cell) ≡ false →
      Machin.MachinNormalizedOuterCoordinateData
    axis1Coordinate : Grid.isInner (Grid.c1 cell) ≡ false →
      Machin.MachinNormalizedOuterCoordinateData
    axis2Coordinate : Grid.isInner (Grid.c2 cell) ≡ false →
      Machin.MachinNormalizedOuterCoordinateData
    axis3Coordinate : Grid.isInner (Grid.c3 cell) ≡ false →
      Machin.MachinNormalizedOuterCoordinateData

    axis0SineInputs : (outer : Grid.isInner (Grid.c0 cell) ≡ false) →
      Sine.ConcreteTwoBallSineInputs elementary
        (Machin.angle (axis0Coordinate outer))
    axis1SineInputs : (outer : Grid.isInner (Grid.c1 cell) ≡ false) →
      Sine.ConcreteTwoBallSineInputs elementary
        (Machin.angle (axis1Coordinate outer))
    axis2SineInputs : (outer : Grid.isInner (Grid.c2 cell) ≡ false) →
      Sine.ConcreteTwoBallSineInputs elementary
        (Machin.angle (axis2Coordinate outer))
    axis3SineInputs : (outer : Grid.isInner (Grid.c3 cell) ≡ false) →
      Sine.ConcreteTwoBallSineInputs elementary
        (Machin.angle (axis3Coordinate outer))

    -- Same-object weld: the component in the literal Wilson atom is exactly the
    -- constructive component to which the outer-sine theorem was applied.
    axis0ComponentIdentified : (outer : Grid.isInner (Grid.c0 cell) ≡ false) →
      Bishop._≃_
        (OuterSine.hatSquare elementary (Machin.angle (axis0Coordinate outer)))
        (Canonical.scaledSineSquareValue trig role Eval.axis0)
    axis1ComponentIdentified : (outer : Grid.isInner (Grid.c1 cell) ≡ false) →
      Bishop._≃_
        (OuterSine.hatSquare elementary (Machin.angle (axis1Coordinate outer)))
        (Canonical.scaledSineSquareValue trig role Eval.axis1)
    axis2ComponentIdentified : (outer : Grid.isInner (Grid.c2 cell) ≡ false) →
      Bishop._≃_
        (OuterSine.hatSquare elementary (Machin.angle (axis2Coordinate outer)))
        (Canonical.scaledSineSquareValue trig role Eval.axis2)
    axis3ComponentIdentified : (outer : Grid.isInner (Grid.c3 cell) ≡ false) →
      Bishop._≃_
        (OuterSine.hatSquare elementary (Machin.angle (axis3Coordinate outer)))
        (Canonical.scaledSineSquareValue trig role Eval.axis3)
open MachinOuterSineCanonicalWeld public

axis0FixedGap :
  ∀ {trig role cell}
    (weld : MachinOuterSineCanonicalWeld trig role cell)
    (outer : Grid.isInner (Grid.c0 cell) ≡ false) →
  Bishop._≤_
    (OuterSine.embed OuterSine.hatSquareLower)
    (Canonical.scaledSineSquareValue trig role Eval.axis0)
axis0FixedGap weld outer =
  let coordinate = axis0Coordinate weld outer
      raw = OuterSine.hatComponentSquareAboveFixedGap
        (axis0SineInputs weld outer)
        (Machin.machinNormalizedAngleLower coordinate)
        (Machin.machinNormalizedAngleUpper coordinate)
  in BishopP.≤-respʳ-≃ (axis0ComponentIdentified weld outer) raw

axis1FixedGap :
  ∀ {trig role cell}
    (weld : MachinOuterSineCanonicalWeld trig role cell)
    (outer : Grid.isInner (Grid.c1 cell) ≡ false) →
  Bishop._≤_
    (OuterSine.embed OuterSine.hatSquareLower)
    (Canonical.scaledSineSquareValue trig role Eval.axis1)
axis1FixedGap weld outer =
  let coordinate = axis1Coordinate weld outer
      raw = OuterSine.hatComponentSquareAboveFixedGap
        (axis1SineInputs weld outer)
        (Machin.machinNormalizedAngleLower coordinate)
        (Machin.machinNormalizedAngleUpper coordinate)
  in BishopP.≤-respʳ-≃ (axis1ComponentIdentified weld outer) raw

axis2FixedGap :
  ∀ {trig role cell}
    (weld : MachinOuterSineCanonicalWeld trig role cell)
    (outer : Grid.isInner (Grid.c2 cell) ≡ false) →
  Bishop._≤_
    (OuterSine.embed OuterSine.hatSquareLower)
    (Canonical.scaledSineSquareValue trig role Eval.axis2)
axis2FixedGap weld outer =
  let coordinate = axis2Coordinate weld outer
      raw = OuterSine.hatComponentSquareAboveFixedGap
        (axis2SineInputs weld outer)
        (Machin.machinNormalizedAngleLower coordinate)
        (Machin.machinNormalizedAngleUpper coordinate)
  in BishopP.≤-respʳ-≃ (axis2ComponentIdentified weld outer) raw

axis3FixedGap :
  ∀ {trig role cell}
    (weld : MachinOuterSineCanonicalWeld trig role cell)
    (outer : Grid.isInner (Grid.c3 cell) ≡ false) →
  Bishop._≤_
    (OuterSine.embed OuterSine.hatSquareLower)
    (Canonical.scaledSineSquareValue trig role Eval.axis3)
axis3FixedGap weld outer =
  let coordinate = axis3Coordinate weld outer
      raw = OuterSine.hatComponentSquareAboveFixedGap
        (axis3SineInputs weld outer)
        (Machin.machinNormalizedAngleLower coordinate)
        (Machin.machinNormalizedAngleUpper coordinate)
  in BishopP.≤-respʳ-≃ (axis3ComponentIdentified weld outer) raw

asSelectedOuterGap :
  ∀ {trig role cell} →
  MachinOuterSineCanonicalWeld trig role cell →
  RegularGap.SelectedOuterBishopGap trig role cell
asSelectedOuterGap weld = record
  { RegularGap.SelectedOuterBishopGap.gap =
      OuterSine.embed OuterSine.hatSquareLower
  ; RegularGap.SelectedOuterBishopGap.gapAtAxis0 = axis0FixedGap weld
  ; RegularGap.SelectedOuterBishopGap.gapAtAxis1 = axis1FixedGap weld
  ; RegularGap.SelectedOuterBishopGap.gapAtAxis2 = axis2FixedGap weld
  ; RegularGap.SelectedOuterBishopGap.gapAtAxis3 = axis3FixedGap weld
  }

machinOuterSineWeldGivesRegularWilsonGap :
  ∀ {trig role cell}
    (weld : MachinOuterSineCanonicalWeld trig role cell) →
  Grid.allInner cell ≡ false →
  Bishop._≤_
    (OuterSine.embed OuterSine.hatSquareLower)
    (Canonical.hatMomentumValue trig role)
machinOuterSineWeldGivesRegularWilsonGap weld regular =
  RegularGap.selectedOuterGapBelowHatMomentum
    (asSelectedOuterGap weld) regular

machinOuterSineToCanonicalComponentGapLevel : ProofLevel
machinOuterSineToCanonicalComponentGapLevel = machineChecked

machinOuterSineToRegularWilsonGapLevel : ProofLevel
machinOuterSineToRegularWilsonGapLevel = machineChecked

-- Remaining physical producer is now purely materialization: construct the
-- canonical per-box Fourier coordinate/angle and show the literal sine-half atom
-- is the same Bishop sine object.  No new trigonometric estimate is required.
physicalCanonicalBoxSineMaterializationLevel : ProofLevel
physicalCanonicalBoxSineMaterializationLevel = conditional
