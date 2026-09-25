module DASHI.Foundations.RelationalObserverNonaryD4DecompositionExact where

------------------------------------------------------------------------
-- LITERAL D4 ACTION ON THE 3x3 OBSERVER CHART
--
-- DASHI CONTRIBUTION
--
-- Conjugate the existing exact D4 action on NineCell through the exact
-- observer-cell bijection.  Then reuse the already-proved raw nine-cell
-- permutation decomposition:
--
--   R^9 = 3 A1 + 0 A2 + B1 + B2 + 2 E.
--
-- This is a representation-theoretic statement about the finite square chart;
-- it creates no psychological semantics.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Biology.D4NineCellOrbitCompressionExact as D4
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as Candidate

rotateObserver90 : Observer.ObserverCell → Observer.ObserverCell
rotateObserver90 cell =
  Observer.nineCellToObserverCell
    (D4.rotate90 (Observer.observerCellToNineCell cell))

reflectObserverVertical : Observer.ObserverCell → Observer.ObserverCell
reflectObserverVertical cell =
  Observer.nineCellToObserverCell
    (D4.reflectVertical (Observer.observerCellToNineCell cell))

rotateObserverFourTimes :
  (cell : Observer.ObserverCell) →
  rotateObserver90
    (rotateObserver90
      (rotateObserver90
        (rotateObserver90 cell)))
  ≡ cell
rotateObserverFourTimes cell
  rewrite Observer.observerCellRoundTrip cell = refl

reflectObserverInvolutive :
  (cell : Observer.ObserverCell) →
  reflectObserverVertical (reflectObserverVertical cell) ≡ cell
reflectObserverInvolutive cell
  rewrite Observer.observerCellRoundTrip cell = refl

observerIrrepMultiplicity : Candidate.D4IrrepKind → Nat
observerIrrepMultiplicity = Candidate.rawNineMultiplicity

observerA1Multiplicity :
  observerIrrepMultiplicity Candidate.A1 ≡ 3
observerA1Multiplicity = refl

observerA2Multiplicity :
  observerIrrepMultiplicity Candidate.A2 ≡ 0
observerA2Multiplicity = refl

observerB1Multiplicity :
  observerIrrepMultiplicity Candidate.B1 ≡ 1
observerB1Multiplicity = refl

observerB2Multiplicity :
  observerIrrepMultiplicity Candidate.B2 ≡ 1
observerB2Multiplicity = refl

observerEMultiplicity :
  observerIrrepMultiplicity Candidate.E2 ≡ 2
observerEMultiplicity = refl

observerPermutationDimension :
  Candidate.rawNineRepresentationDimension ≡ 9
observerPermutationDimension =
  Candidate.rawNineRepresentationDimensionIsNine

record ObserverNonaryD4Boundary : Set where
  constructor observer-nonary-d4-boundary
  field
    literalD4ActionTransportedToObserverChart : Bool
    rawNineDecompositionDimensionExact : Bool
    reflectionOddA2PresentInBarePermutationCarrier : Bool
    D4DecompositionCreatesPsychologicalMeaning : Bool
    D4DecompositionEqualsFiveModePhaseQuotient : Bool

canonicalObserverNonaryD4Boundary : ObserverNonaryD4Boundary
canonicalObserverNonaryD4Boundary =
  observer-nonary-d4-boundary true true false false false
