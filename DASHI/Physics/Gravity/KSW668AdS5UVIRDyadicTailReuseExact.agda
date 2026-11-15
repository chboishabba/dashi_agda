module DASHI.Physics.Gravity.KSW668AdS5UVIRDyadicTailReuseExact where

------------------------------------------------------------------------
-- KSW AdS5 exact scale separation: REUSE existing DASHI dyadic-tail
-- algebra, with a physically unproved Fourier cutoff increment premise.
--
-- Source original: KSW668 a=t compact TT anisotropic stress.
-- One source scalar bump is C-infinity and spatially compact.
-- The degree-four TT operator suppresses k=0; applying two further
-- spatial derivatives gives k^6 at amplitude level. A 3D Fourier L2
-- radial measure then has k^10, k^14 weighted source moments.
--
-- This module PROVES only the conditional finite dyadic tail reuse.
-- It does NOT claim the physical adjacent-cutoff bound C*2^-j,
-- a source->receiver transfer estimate, a Green kernel, Agda continuum
-- geometry or full UV numerical convergence.
--
-- Imported theorem:
-- BalabanClayDyadicCutoffTailExact.finiteDistanceBelowDoubleDyadic.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Rational.Base using (ℚ; _≤_; _*_)
import DASHI.Physics.YangMills.BalabanClayDyadicCutoffTailExact as Tail

kswOriginalFiniteDyadicSourceTail :
  ∀ {State : Set}
  (dataSet : Tail.DyadicIncrementSequence State)
  (start count : Nat) →
  Tail.Distance dataSet
    (Tail.stateAt dataSet start)
    (Tail.stateAt dataSet (start + count))
  ≤
  Tail.coefficient dataSet
    * (Tail.two * Tail.dyadic start)
kswOriginalFiniteDyadicSourceTail dataSet start count =
  Tail.finiteDistanceBelowDoubleDyadic dataSet start count

-- The physical promotion must inhabit the imported DyadicIncrementSequence
-- with an adjacentIncrement bound for the ACTUAL original AdS5 source
-- or receiver. An arbitrary instance is not evidence that such an
-- analytic Fourier/Weyl bound has been established.
