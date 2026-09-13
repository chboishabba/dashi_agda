module DASHI.Moonshine.JInvariantJCoarseFineFrickeBoundaryTransportBidiExact where

------------------------------------------------------------------------
-- FINITE FRICKE TRANSPORT ACROSS THE jCOARSE/jFINE FIBRE BOUNDARY
--
-- The existing 1+10 chart carries the exact finite complement involution
--
--   j9 <-> d0,  d1 <-> d8,  d2 <-> d7,  d3 <-> d6,  d4 <-> d5.
--
-- The exact 11-trit chart shift moves the j9 fine value into the second coarse
-- trit, leaving d0..d8 as the relative nine-coordinate fine field.  Therefore
-- conjugating the finite Fricke action through that chart shift necessarily
-- exchanges information between coarse and fine coordinates.  It is not an
-- independent action on the fine fibre.
--
-- This is a finite DASHI transport theorem only.  It does not identify the
-- finite complement involution with the analytic Fricke involution on a
-- modular curve, nor with the rendered Klein-j seam.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.ModularCoarseFineAddressFibrationExact as Outer
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Nonary
import DASHI.Biology.TernaryPhaseQuotientJCoarseBridgeExact as Coarse
import DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact as Phase
import DASHI.Moonshine.JInvariantJCoarseFineElevenTritChartShiftExact as Chart

------------------------------------------------------------------------
-- 1. Fricke action in the 1+10 chart and transport into the 2+9 chart.
------------------------------------------------------------------------

outerFiniteFricke : Chart.OuterOnePlusTen -> Chart.OuterOnePlusTen
outerFiniteFricke (coarse , fine) =
  coarse , Outer.finiteFrickePullback fine

transportedFiniteFricke : Chart.JTwoPlusNine -> Chart.JTwoPlusNine
transportedFiniteFricke state =
  Chart.oneTenToTwoNine
    (outerFiniteFricke (Chart.twoNineToOneTen state))

------------------------------------------------------------------------
-- 2. The first coarse trit is unchanged.
------------------------------------------------------------------------

firstCoarseAfterTransport :
  (state : Chart.JTwoPlusNine) ->
  Harmonic.firstTrit (Chart.jCoarsePair (transportedFiniteFricke state))
  ≡ Harmonic.firstTrit (Chart.jCoarsePair state)
firstCoarseAfterTransport
  (Harmonic.balancedPair first second , field) = refl

------------------------------------------------------------------------
-- 3. The second coarse trit becomes the old d0 fine value.
--
-- q00 = (-,-) is the ordinary phase point corresponding to d0.
------------------------------------------------------------------------

q00 : Phase.PhaseQuotient9
q00 = Base.tri-low , Base.tri-low

secondCoarseAfterTransport :
  (state : Chart.JTwoPlusNine) ->
  Harmonic.secondTrit (Chart.jCoarsePair (transportedFiniteFricke state))
  ≡
  Coarse.triToBalanced (Chart.jRelativeFine state q00)
secondCoarseAfterTransport
  (Harmonic.balancedPair first second , field) = refl

------------------------------------------------------------------------
-- 4. Conversely, q00 in the transported fine field becomes the old second
-- coarse trit.  Thus Fricke literally exchanges one coordinate across the
-- coarse/fine boundary.
------------------------------------------------------------------------

q00FineAfterTransport :
  (state : Chart.JTwoPlusNine) ->
  Chart.jRelativeFine (transportedFiniteFricke state) q00
  ≡
  Coarse.balancedToTri
    (Harmonic.secondTrit (Chart.jCoarsePair state))
q00FineAfterTransport
  (Harmonic.balancedPair first second , field) = refl

record BoundaryExchangeReceipt (state : Chart.JTwoPlusNine) : Set where
  constructor boundary-exchange-receipt
  field
    firstCoarsePreserved :
      Harmonic.firstTrit (Chart.jCoarsePair (transportedFiniteFricke state))
      ≡ Harmonic.firstTrit (Chart.jCoarsePair state)
    secondCoarseComesFromFineQ00 :
      Harmonic.secondTrit (Chart.jCoarsePair (transportedFiniteFricke state))
      ≡ Coarse.triToBalanced (Chart.jRelativeFine state q00)
    fineQ00ComesFromSecondCoarse :
      Chart.jRelativeFine (transportedFiniteFricke state) q00
      ≡ Coarse.balancedToTri
          (Harmonic.secondTrit (Chart.jCoarsePair state))

canonicalBoundaryExchange :
  (state : Chart.JTwoPlusNine) -> BoundaryExchangeReceipt state
canonicalBoundaryExchange state =
  boundary-exchange-receipt
    (firstCoarseAfterTransport state)
    (secondCoarseAfterTransport state)
    (q00FineAfterTransport state)

------------------------------------------------------------------------
-- 5. Two applications restore the boundary coordinates.
------------------------------------------------------------------------

secondCoarseTwoTransports :
  (state : Chart.JTwoPlusNine) ->
  Harmonic.secondTrit
    (Chart.jCoarsePair
      (transportedFiniteFricke (transportedFiniteFricke state)))
  ≡ Harmonic.secondTrit (Chart.jCoarsePair state)
secondCoarseTwoTransports
  (Harmonic.balancedPair first second , field)
  rewrite Coarse.triAfterBalanced second = refl

q00FineTwoTransports :
  (state : Chart.JTwoPlusNine) ->
  Chart.jRelativeFine
    (transportedFiniteFricke (transportedFiniteFricke state)) q00
  ≡ Chart.jRelativeFine state q00
q00FineTwoTransports
  (Harmonic.balancedPair first second , field)
  rewrite Coarse.balancedAfterTri (field q00) = refl

------------------------------------------------------------------------
-- 6. Independence no-go at the typed-coordinate level.
--
-- A transport that preserved the second coarse coordinate by construction
-- could not realise this boundary exchange for arbitrary states unless the
-- q00 fine value happened to equal that coordinate.  We retain this as an
-- explicit model distinction rather than postulating inequality of arbitrary
-- trits constructively.
------------------------------------------------------------------------

record IndependentFineOnlyTransportBoundary : Set where
  constructor independent-fine-only-transport-boundary
  field
    transportedFrickePreservesSecondCoarseByDefinition : Bool
    transportedFrickeExchangesSecondCoarseWithFineQ00 : Bool
    thereforeFiniteTransportIsPureFinePermutation : Bool
    analyticFrickeIdentified : Bool
    renderedSeamIdentified : Bool

canonicalIndependentFineOnlyTransportBoundary :
  IndependentFineOnlyTransportBoundary
canonicalIndependentFineOnlyTransportBoundary =
  independent-fine-only-transport-boundary
    false true false false false

------------------------------------------------------------------------
-- 7. Frontier.
------------------------------------------------------------------------

data FrickeBoundaryResidual : Set where
  missingAnalyticFrickeToFiniteTransportIntertwiner : FrickeBoundaryResidual
  missingRenderedSeamToStructuredJAbsolute : FrickeBoundaryResidual
  missingFineSensitiveAnalyticGluingSquare : FrickeBoundaryResidual

record FrickeBoundaryTransportFrontier : Set where
  constructor fricke-boundary-transport-frontier
  field
    finiteComplementInvolutionExisting : Bool
    elevenTritChartShiftExisting : Bool
    coarseFineBoundaryExchangeExact : Bool
    boundaryExchangeTwoStepRestorationExact : Bool
    pureFinePermutationModelRejectedForFiniteTransport : Bool
    analyticFrickeIntertwinerExact : Bool
    renderedSeamSameObjectExact : Bool
    firstResidual : FrickeBoundaryResidual

canonicalFrickeBoundaryTransportFrontier : FrickeBoundaryTransportFrontier
canonicalFrickeBoundaryTransportFrontier =
  fricke-boundary-transport-frontier
    true true true true true false false
    missingAnalyticFrickeToFiniteTransportIntertwiner
