module DASHI.Moonshine.JInvariantJCoarseFineElevenTritChartShiftExact where

------------------------------------------------------------------------
-- EXACT 11-TRIT CHART SHIFT
--
-- Existing owners expose two decompositions of the same 11-trit absolute
-- address depth:
--
--   outer chart : 1 coarse trit + 10-sector ternary fine field
--   j chart     : 2 coarse trits + 9-state ternary relative fine field
--
-- The distinguished completion-j sector gives a canonical boundary move:
--
--   (c ; f_d0 ... f_d8 , f_j)
--       <->
--   ((c , f_j) ; q |-> f_(ordinary(q))).
--
-- The remaining nine sectors are exactly the ordinary balanced-pair channels,
-- already equivalent to PhaseQuotient9.  Pointwise inverse laws avoid any
-- function-extensionality postulate.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.JFinePhaseQuotientFieldExact as Fine
import DASHI.Biology.ModularCoarseFineAddressFibrationExact as Outer
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Nonary
import DASHI.Biology.TernaryPhaseQuotientJCoarseBridgeExact as Coarse
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase

------------------------------------------------------------------------
-- 1. Ordinary nine-sector correspondence.
------------------------------------------------------------------------

phaseToOrdinaryDecimal : Phase.PhaseQuotient9 -> Nonary.DecimalCompletionState
phaseToOrdinaryDecimal q =
  Nonary.fromCoarseChannel (Coarse.phaseQuotientToOrdinaryCoarse q)

ordinaryDecimalToPhase : Nonary.DecimalCompletionState -> Phase.PhaseQuotient9
ordinaryDecimalToPhase Nonary.d0 = Base.tri-low , Base.tri-low
ordinaryDecimalToPhase Nonary.d1 = Base.tri-low , Base.tri-mid
ordinaryDecimalToPhase Nonary.d2 = Base.tri-low , Base.tri-high
ordinaryDecimalToPhase Nonary.d3 = Base.tri-mid , Base.tri-low
ordinaryDecimalToPhase Nonary.d4 = Base.tri-mid , Base.tri-mid
ordinaryDecimalToPhase Nonary.d5 = Base.tri-mid , Base.tri-high
ordinaryDecimalToPhase Nonary.d6 = Base.tri-high , Base.tri-low
ordinaryDecimalToPhase Nonary.d7 = Base.tri-high , Base.tri-mid
ordinaryDecimalToPhase Nonary.d8 = Base.tri-high , Base.tri-high
-- Completion is handled separately by the chart shift and never consumed as
-- an ordinary phase point.  This total branch is therefore observational only.
ordinaryDecimalToPhase Nonary.j9 = Base.tri-low , Base.tri-low

phaseOrdinaryRoundTrip :
  (q : Phase.PhaseQuotient9) ->
  ordinaryDecimalToPhase (phaseToOrdinaryDecimal q) ≡ q
phaseOrdinaryRoundTrip (Base.tri-low , Base.tri-low) = refl
phaseOrdinaryRoundTrip (Base.tri-low , Base.tri-mid) = refl
phaseOrdinaryRoundTrip (Base.tri-low , Base.tri-high) = refl
phaseOrdinaryRoundTrip (Base.tri-mid , Base.tri-low) = refl
phaseOrdinaryRoundTrip (Base.tri-mid , Base.tri-mid) = refl
phaseOrdinaryRoundTrip (Base.tri-mid , Base.tri-high) = refl
phaseOrdinaryRoundTrip (Base.tri-high , Base.tri-low) = refl
phaseOrdinaryRoundTrip (Base.tri-high , Base.tri-mid) = refl
phaseOrdinaryRoundTrip (Base.tri-high , Base.tri-high) = refl

------------------------------------------------------------------------
-- 2. Two chart carriers.
------------------------------------------------------------------------

OuterOnePlusTen : Set
OuterOnePlusTen = Outer.CoarseAddress × Outer.FineAddress

JTwoPlusNine : Set
JTwoPlusNine = Harmonic.BalancedPair × Fine.PhaseFineField

outerCoarse : OuterOnePlusTen -> Harmonic.BalancedTrit
outerCoarse (coarse , fine) = coarse

outerFine : OuterOnePlusTen -> Outer.FineAddress
outerFine (coarse , fine) = fine

jCoarsePair : JTwoPlusNine -> Harmonic.BalancedPair
jCoarsePair (coarse , fine) = coarse

jRelativeFine : JTwoPlusNine -> Fine.PhaseFineField
jRelativeFine (coarse , fine) = fine

------------------------------------------------------------------------
-- 3. 1+10 -> 2+9.
------------------------------------------------------------------------

ordinaryFineFromOuter : Outer.FineAddress -> Fine.PhaseFineField
ordinaryFineFromOuter fine q =
  Coarse.balancedToTri (fine (phaseToOrdinaryDecimal q))

oneTenToTwoNine : OuterOnePlusTen -> JTwoPlusNine
oneTenToTwoNine (coarse , fine) =
  Harmonic.balancedPair coarse (fine Nonary.j9)
  , ordinaryFineFromOuter fine

------------------------------------------------------------------------
-- 4. 2+9 -> 1+10.
------------------------------------------------------------------------

outerFineFromJ :
  Harmonic.BalancedTrit -> Fine.PhaseFineField -> Outer.FineAddress
outerFineFromJ completion field Nonary.d0 =
  Coarse.triToBalanced (field (Base.tri-low , Base.tri-low))
outerFineFromJ completion field Nonary.d1 =
  Coarse.triToBalanced (field (Base.tri-low , Base.tri-mid))
outerFineFromJ completion field Nonary.d2 =
  Coarse.triToBalanced (field (Base.tri-low , Base.tri-high))
outerFineFromJ completion field Nonary.d3 =
  Coarse.triToBalanced (field (Base.tri-mid , Base.tri-low))
outerFineFromJ completion field Nonary.d4 =
  Coarse.triToBalanced (field (Base.tri-mid , Base.tri-mid))
outerFineFromJ completion field Nonary.d5 =
  Coarse.triToBalanced (field (Base.tri-mid , Base.tri-high))
outerFineFromJ completion field Nonary.d6 =
  Coarse.triToBalanced (field (Base.tri-high , Base.tri-low))
outerFineFromJ completion field Nonary.d7 =
  Coarse.triToBalanced (field (Base.tri-high , Base.tri-mid))
outerFineFromJ completion field Nonary.d8 =
  Coarse.triToBalanced (field (Base.tri-high , Base.tri-high))
outerFineFromJ completion field Nonary.j9 = completion

twoNineToOneTen : JTwoPlusNine -> OuterOnePlusTen
twoNineToOneTen
  (Harmonic.balancedPair first second , field) =
  first , outerFineFromJ second field

------------------------------------------------------------------------
-- 5. Pointwise two-sided laws.
------------------------------------------------------------------------

outerCoarseRoundTrip :
  (state : OuterOnePlusTen) ->
  outerCoarse (twoNineToOneTen (oneTenToTwoNine state))
  ≡ outerCoarse state
outerCoarseRoundTrip (coarse , fine) = refl

outerFineRoundTripPointwise :
  (state : OuterOnePlusTen) ->
  (sector : Nonary.DecimalCompletionState) ->
  outerFine (twoNineToOneTen (oneTenToTwoNine state)) sector
  ≡ outerFine state sector
outerFineRoundTripPointwise (coarse , fine) Nonary.d0 =
  Coarse.triAfterBalanced (fine Nonary.d0)
outerFineRoundTripPointwise (coarse , fine) Nonary.d1 =
  Coarse.triAfterBalanced (fine Nonary.d1)
outerFineRoundTripPointwise (coarse , fine) Nonary.d2 =
  Coarse.triAfterBalanced (fine Nonary.d2)
outerFineRoundTripPointwise (coarse , fine) Nonary.d3 =
  Coarse.triAfterBalanced (fine Nonary.d3)
outerFineRoundTripPointwise (coarse , fine) Nonary.d4 =
  Coarse.triAfterBalanced (fine Nonary.d4)
outerFineRoundTripPointwise (coarse , fine) Nonary.d5 =
  Coarse.triAfterBalanced (fine Nonary.d5)
outerFineRoundTripPointwise (coarse , fine) Nonary.d6 =
  Coarse.triAfterBalanced (fine Nonary.d6)
outerFineRoundTripPointwise (coarse , fine) Nonary.d7 =
  Coarse.triAfterBalanced (fine Nonary.d7)
outerFineRoundTripPointwise (coarse , fine) Nonary.d8 =
  Coarse.triAfterBalanced (fine Nonary.d8)
outerFineRoundTripPointwise (coarse , fine) Nonary.j9 = refl

jCoarseRoundTrip :
  (state : JTwoPlusNine) ->
  jCoarsePair (oneTenToTwoNine (twoNineToOneTen state))
  ≡ jCoarsePair state
jCoarseRoundTrip
  (Harmonic.balancedPair first second , field) = refl

jFineRoundTripPointwise :
  (state : JTwoPlusNine) ->
  (q : Phase.PhaseQuotient9) ->
  jRelativeFine (oneTenToTwoNine (twoNineToOneTen state)) q
  ≡ jRelativeFine state q
jFineRoundTripPointwise
  (Harmonic.balancedPair first second , field)
  (Base.tri-low , Base.tri-low) =
  Coarse.balancedAfterTri (field (Base.tri-low , Base.tri-low))
jFineRoundTripPointwise
  (Harmonic.balancedPair first second , field)
  (Base.tri-low , Base.tri-mid) =
  Coarse.balancedAfterTri (field (Base.tri-low , Base.tri-mid))
jFineRoundTripPointwise
  (Harmonic.balancedPair first second , field)
  (Base.tri-low , Base.tri-high) =
  Coarse.balancedAfterTri (field (Base.tri-low , Base.tri-high))
jFineRoundTripPointwise
  (Harmonic.balancedPair first second , field)
  (Base.tri-mid , Base.tri-low) =
  Coarse.balancedAfterTri (field (Base.tri-mid , Base.tri-low))
jFineRoundTripPointwise
  (Harmonic.balancedPair first second , field)
  (Base.tri-mid , Base.tri-mid) =
  Coarse.balancedAfterTri (field (Base.tri-mid , Base.tri-mid))
jFineRoundTripPointwise
  (Harmonic.balancedPair first second , field)
  (Base.tri-mid , Base.tri-high) =
  Coarse.balancedAfterTri (field (Base.tri-mid , Base.tri-high))
jFineRoundTripPointwise
  (Harmonic.balancedPair first second , field)
  (Base.tri-high , Base.tri-low) =
  Coarse.balancedAfterTri (field (Base.tri-high , Base.tri-low))
jFineRoundTripPointwise
  (Harmonic.balancedPair first second , field)
  (Base.tri-high , Base.tri-mid) =
  Coarse.balancedAfterTri (field (Base.tri-high , Base.tri-mid))
jFineRoundTripPointwise
  (Harmonic.balancedPair first second , field)
  (Base.tri-high , Base.tri-high) =
  Coarse.balancedAfterTri (field (Base.tri-high , Base.tri-high))

------------------------------------------------------------------------
-- 6. Absolute depth/cardinality alignment.
------------------------------------------------------------------------

outerAbsoluteDepthIsEleven : Outer.jAbsoluteAddressDepth ≡ 11
outerAbsoluteDepthIsEleven = refl

jAbsoluteCardinalityIsThreePowerEleven : Fine.phaseAbsoluteCardinality ≡ 177147
jAbsoluteCardinalityIsThreePowerEleven = refl

outerAbsoluteCardinalityIsThreePowerEleven : Outer.jAbsoluteStateCount ≡ 177147
outerAbsoluteCardinalityIsThreePowerEleven = refl

absoluteCardinalitiesAgree :
  Outer.jAbsoluteStateCount ≡ Fine.phaseAbsoluteCardinality
absoluteCardinalitiesAgree = refl

------------------------------------------------------------------------
-- 7. Frontier.
------------------------------------------------------------------------

record ElevenTritChartShiftFrontier : Set where
  constructor eleven-trit-chart-shift-frontier
  field
    completionJProvidesCanonicalBoundaryCoordinate : Bool
    ordinaryNineMapsExactlyToPhaseQuotientNine : Bool
    onePlusTenToTwoPlusNineConstructed : Bool
    outerRoundTripPointwise : Bool
    jRoundTripPointwise : Bool
    functionExtensionalityRequired : Bool
    chartShiftIsLiteralModularCurveTheorem : Bool

canonicalElevenTritChartShiftFrontier : ElevenTritChartShiftFrontier
canonicalElevenTritChartShiftFrontier =
  eleven-trit-chart-shift-frontier
    true true true true true false false
