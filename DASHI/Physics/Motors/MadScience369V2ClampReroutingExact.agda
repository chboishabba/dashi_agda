module DASHI.Physics.Motors.MadScience369V2ClampReroutingExact where

-- Original, source-independent finite conservation theorem for a pulse
-- recovery circuit.  @madscience369's actual V2 clamp and wiring are unknown.
-- Don Smith/Filsinger, Holmstrom and Slobodian designs are DISTINCT sources.
-- Exact natural-number accounting is NOT nonlinear continuum electromagnetics.
-- A physical experiment must pay the clamp partition premise.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Recovery

plusAssoc : (a b c : Nat) → (a + b) + c ≡ a + (b + c)
plusAssoc zero b c = refl
plusAssoc (suc a) b c rewrite plusAssoc a b c = refl

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- Initially a clamp dissipates beforeClamp.  A physically evidenced
-- rerouting stage could recover part as useful work while retaining
-- additional switching loss and unrecovered clamp heat.  The split
-- equality is an EXPLICIT physical modelling premise, not inferred from
-- a video. No fuel, actuator, storage depletion or heat source is omitted.
record ClampRecoveryPartition : Set where
  constructor clampRecoveryPartition
  field
    beforeUseful beforeClamp recoveredUseful : Nat
    extraSwitchLoss unrecoveredClampHeat otherLoss : Nat
    clampSplit :
      beforeClamp ≡ recoveredUseful + (extraSwitchLoss + unrecoveredClampHeat)

open ClampRecoveryPartition public

sourceBefore : ClampRecoveryPartition → Nat
sourceBefore r = beforeUseful r + (beforeClamp r + otherLoss r)

sourceAfter : ClampRecoveryPartition → Nat
sourceAfter r =
  (beforeUseful r + recoveredUseful r) +
    ((extraSwitchLoss r + unrecoveredClampHeat r) + otherLoss r)

-- This theorem derives equality of complete input budgets from a
-- partition of an EXISTING clamp dissipation, rather than assuming two
-- unrelated energy ledgers are both balanced.
recoveredClampPreservesInput :
  (r : ClampRecoveryPartition) → sourceBefore r ≡ sourceAfter r
recoveredClampPreservesInput r
  rewrite clampSplit r
        | plusAssoc (recoveredUseful r)
                    (extraSwitchLoss r + unrecoveredClampHeat r)
                    (otherLoss r)
  = sym (plusAssoc (beforeUseful r)
                   (recoveredUseful r)
                   ((extraSwitchLoss r + unrecoveredClampHeat r) + otherLoss r))

-- Conditional clamp harvesting strictly cannot DECREASE useful work
-- in the no-extra-source model, but may offer no benefit if recovered=0.
usefulAfterNotLess : (r : ClampRecoveryPartition) →
  Recovery._≤_ (beforeUseful r) (beforeUseful r + recoveredUseful r)
usefulAfterNotLess r = Recovery.≤-append (beforeUseful r) (recoveredUseful r)

sampleRecovery : ClampRecoveryPartition
sampleRecovery = clampRecoveryPartition 31 6 3 1 2 9 refl

sampleNoAddedInput : sourceBefore sampleRecovery ≡ sourceAfter sampleRecovery
sampleNoAddedInput = recoveredClampPreservesInput sampleRecovery

sampleRecoverIncreasesLoad : Recovery._≤_ 31 34
sampleRecoverIncreasesLoad = usefulAfterNotLess sampleRecovery

-- Intentionally no declaration asserting this partition for the original V2.
