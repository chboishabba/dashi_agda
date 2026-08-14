module DASHI.Biology.Physical.DNAHelixTernaryQuantizationResidualExact where

------------------------------------------------------------------------
-- PNF-safe bridge between the four-state finite DNA helix phase skeleton and
-- a three-state observation carrier.
--
-- 4 is not identified with 3.  The coarse ternary observation merges one
-- phase fibre, and a one-bit residual is retained only there so that the fine
-- helix phase can be reopened exactly.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.DNAHelixDihedralExact as Helix
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

Trit : Set
Trit = Wheel.DepthWheelPhase

quantizePhase : Helix.Phase4 → Trit
quantizePhase Helix.p0 = Wheel.phase-0
quantizePhase Helix.p1 = Wheel.phase-1
quantizePhase Helix.p2 = Wheel.phase-2
quantizePhase Helix.p3 = Wheel.phase-2

------------------------------------------------------------------------
-- Adaptive residual: only the overloaded phase-2 fibre needs one bit.
------------------------------------------------------------------------

data PhaseResidual : Trit → Set where
  unique0 : PhaseResidual Wheel.phase-0
  unique1 : PhaseResidual Wheel.phase-1
  lower2 upper2 : PhaseResidual Wheel.phase-2

residual : (p : Helix.Phase4) → PhaseResidual (quantizePhase p)
residual Helix.p0 = unique0
residual Helix.p1 = unique1
residual Helix.p2 = lower2
residual Helix.p3 = upper2

reopen : (t : Trit) → PhaseResidual t → Helix.Phase4
reopen Wheel.phase-0 unique0 = Helix.p0
reopen Wheel.phase-1 unique1 = Helix.p1
reopen Wheel.phase-2 lower2 = Helix.p2
reopen Wheel.phase-2 upper2 = Helix.p3

reopenQuantizedPhaseExactly :
  (p : Helix.Phase4) → reopen (quantizePhase p) (residual p) ≡ p
reopenQuantizedPhaseExactly Helix.p0 = refl
reopenQuantizedPhaseExactly Helix.p1 = refl
reopenQuantizedPhaseExactly Helix.p2 = refl
reopenQuantizedPhaseExactly Helix.p3 = refl

------------------------------------------------------------------------
-- Coarse collision is real, not merely a type-level possibility.
------------------------------------------------------------------------

p2p3CollapseToSameTrit :
  quantizePhase Helix.p2 ≡ quantizePhase Helix.p3
p2p3CollapseToSameTrit = refl

lowerUpperResidualsReopenDifferentFinePhases :
  reopen Wheel.phase-2 lower2 ≢ reopen Wheel.phase-2 upper2
lowerUpperResidualsReopenDifferentFinePhases ()

record QuantizedHelixPhase : Set where
  constructor quantizedHelixPhase
  field
    coarse : Trit
    fineResidual : PhaseResidual coarse

open QuantizedHelixPhase public

encode : Helix.Phase4 → QuantizedHelixPhase
encode p = quantizedHelixPhase (quantizePhase p) (residual p)

decode : QuantizedHelixPhase → Helix.Phase4
decode (quantizedHelixPhase t r) = reopen t r

decodeEncodeExact : (p : Helix.Phase4) → decode (encode p) ≡ p
decodeEncodeExact = reopenQuantizedPhaseExactly

------------------------------------------------------------------------
-- This is the precise bridge:
--
--   fine four-state phase -> ternary observation + adaptive residual.
--
-- A later analytic helix may replace Phase4 with calibrated continuous angle;
-- the quotient/reopening obligation remains the same.
------------------------------------------------------------------------
