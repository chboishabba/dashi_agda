module DASHI.Cognition.PNF.GoNoGoActuationGateExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Decision

------------------------------------------------------------------------
-- Literature calibration:
-- Thomas E. Hazy; Michael J. Frank; Randall C. O'Reilly,
-- "Towards an executive without a homunculus: computational models of the
-- prefrontal cortex/basal ganglia system",
-- DOI 10.1098/rstb.2007.2055.
--
-- Finite Go/NoGo competition is a candidate actuation producer.  It remains
-- downstream of cortical/abstract commitment and does not define value.
------------------------------------------------------------------------

data GateEvidence : Set where
  low high : GateEvidence

releaseGate : GateEvidence → GateEvidence → Decision.ActuationGate
releaseGate high low = Decision.released
releaseGate _ _ = Decision.blocked

goDominatesReleases : releaseGate high low ≡ Decision.released
goDominatesReleases = refl

noGoPreventsRelease : releaseGate high high ≡ Decision.blocked
noGoPreventsRelease = refl

sameCommitmentDifferentGoNoGoOutcome :
  Decision.actuate (releaseGate high low) Decision.supportCommitted
  ≡
  Decision.actuate (releaseGate high high) Decision.supportCommitted → ⊥
sameCommitmentDifferentGoNoGoOutcome ()

commitmentRetainedWhenBlocked :
  Decision.commit Decision.supportLead ≡ Decision.supportCommitted
  × Decision.actuate (releaseGate high high) Decision.supportCommitted ≡ Decision.noAction
commitmentRetainedWhenBlocked = refl , refl

record GoNoGoBoundary : Set where
  constructor goNoGoBoundary
  field
    goNoGoDefinesValue : Bool
    goNoGoDefinesCommitment : Bool
    blockedActuationErasesCommitment : Bool

canonicalGoNoGoBoundary : GoNoGoBoundary
canonicalGoNoGoBoundary = goNoGoBoundary false false false
