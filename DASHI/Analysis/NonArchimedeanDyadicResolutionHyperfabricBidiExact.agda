module DASHI.Analysis.NonArchimedeanDyadicResolutionHyperfabricBidiExact where

------------------------------------------------------------------------
-- DYADIC SCALE AS AN EXISTING HYPERFABRIC / REFINEMENT COORDINATE
--
-- Base369BinaryTernaryRefinement already stores binary and ternary refinement
-- depths independently.  The non-Archimedean dyadic level n therefore reuses
-- the pure-binary chart (n,0) rather than creating a new scale ontology.
--
-- This is a chart-level x-pollination only: a resolution coordinate is not a
-- proof that the Base369 carrier is Z/2^nZ, nor that its phase algebra is the
-- source repo's cyclotomic carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369BinaryTernaryRefinement as Refinement

pureDyadicResolution : Nat → Refinement.Resolution23
pureDyadicResolution n = Refinement.resolution23 n 0

pureDyadicBinaryDepth :
  (n : Nat) →
  Refinement.binaryDepth (pureDyadicResolution n) ≡ n
pureDyadicBinaryDepth n = refl

pureDyadicTernaryDepthIsZero :
  (n : Nat) →
  Refinement.ternaryDepth (pureDyadicResolution n) ≡ 0
pureDyadicTernaryDepthIsZero n = refl

nextDyadicScaleIsBinaryRefinement :
  (n : Nat) →
  Refinement.binaryRefine (pureDyadicResolution n)
  ≡ pureDyadicResolution (suc n)
nextDyadicScaleIsBinaryRefinement n = refl

record DyadicResolutionCrossPollinationBoundary : Set where
  constructor dyadicResolutionCrossPollinationBoundary
  field
    binaryDepthCoordinateReused : Bool
    dyadicScaleCreatesNewHyperfabricAxis : Bool
    resolutionCoordinateEqualsCyclicGroupCarrier : Bool
    base369PhaseEqualsDyadicCyclotomicPhase : Bool

canonicalDyadicResolutionCrossPollinationBoundary :
  DyadicResolutionCrossPollinationBoundary
canonicalDyadicResolutionCrossPollinationBoundary =
  dyadicResolutionCrossPollinationBoundary
    true
    false
    false
    false
