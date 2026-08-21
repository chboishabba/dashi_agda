module DASHI.Cognition.PNF.AttentionValueActuationSeparationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.AccessibleCandidateReasoningPipelineExact as Pre
import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Decision

------------------------------------------------------------------------
-- Literature calibration:
-- Ian Krajbich, Carrie Armel, Antonio Rangel,
-- "Visual fixations and the computation and comparison of value in simple
-- choice", DOI 10.1038/nn.2635.
--
-- This finite model separates stored value from attention/access gain.  It is
-- not a quantitative fit of the attentional DDM.
------------------------------------------------------------------------

data Attention : Set where
  attended unattended : Attention

storedValue : Pre.Candidate → Nat
storedValue Pre.supportingCandidate = 2
storedValue Pre.counterCandidate = 2

attentionGain : Attention → Nat
attentionGain attended = 1
attentionGain unattended = 0

-- finite multiplicative gate specialized to equal stored value 2
attendedEvidence : Attention → Pre.Candidate → Nat
attendedEvidence attended c = storedValue c
attendedEvidence unattended c = 0

sameValueDifferentAttentionEvidence :
  storedValue Pre.supportingCandidate ≡ storedValue Pre.counterCandidate
  × attendedEvidence attended Pre.supportingCandidate ≡ 2
  × attendedEvidence unattended Pre.counterCandidate ≡ 0
sameValueDifferentAttentionEvidence = refl , (refl , refl)

attentionChangeDoesNotChangeStoredValue :
  storedValue Pre.counterCandidate ≡ 2
attentionChangeDoesNotChangeStoredValue = refl

attentionAndValueAreDistinctAxes :
  attendedEvidence attended Pre.counterCandidate
  ≡ attendedEvidence unattended Pre.counterCandidate → ⊥
attentionAndValueAreDistinctAxes ()

------------------------------------------------------------------------
-- Value/commitment and release/actuation remain distinct.
------------------------------------------------------------------------

valuedCommittedButBlocked :
  storedValue Pre.supportingCandidate ≡ 2
  × Decision.commit Decision.supportLead ≡ Decision.supportCommitted
  × Decision.actuate Decision.blocked Decision.supportCommitted ≡ Decision.noAction
valuedCommittedButBlocked = refl , (refl , refl)

releaseChangesActionWithoutChangingStoredValue :
  storedValue Pre.supportingCandidate ≡ 2
  × (Decision.actuate Decision.blocked Decision.supportCommitted
     ≡ Decision.actuate Decision.released Decision.supportCommitted → ⊥)
releaseChangesActionWithoutChangingStoredValue =
  refl , Decision.sameCommitmentDifferentActuation

record AttentionValueActuationBoundary : Set where
  constructor attentionValueActuationBoundary
  field
    accessEqualsValue : Bool
    valueEqualsCommitment : Bool
    commitmentEqualsRelease : Bool
    releaseEqualsStoredValue : Bool

canonicalAttentionValueActuationBoundary : AttentionValueActuationBoundary
canonicalAttentionValueActuationBoundary =
  attentionValueActuationBoundary false false false false
