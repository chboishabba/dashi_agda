module DASHI.Cognition.PNF.BoundedEvidenceCommitmentExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

------------------------------------------------------------------------
-- Literature calibration:
-- Joshua I. Gold; Michael N. Shadlen,
-- "The Neural Basis of Decision Making",
-- DOI 10.1146/annurev.neuro.29.051605.113038.
--
-- This finite exact producer captures bounded accumulation and a distinct
-- commitment threshold; it is not a quantitative fit of LIP firing rates.
------------------------------------------------------------------------

data EvidenceLevel : Set where
  e0 e1 e2 : EvidenceLevel

data RelevantContext : Set where
  attendEvidence ignoreEvidence : RelevantContext

data ThresholdCommitment : Set where
  stillDeliberating committed : ThresholdCommitment

increment : EvidenceLevel → EvidenceLevel
increment e0 = e1
increment e1 = e2
increment e2 = e2

contextGate : RelevantContext → EvidenceLevel → EvidenceLevel
contextGate attendEvidence e = increment e
contextGate ignoreEvidence e = e

threshold : EvidenceLevel → ThresholdCommitment
threshold e0 = stillDeliberating
threshold e1 = stillDeliberating
threshold e2 = committed

oneRelevantPulseNotYetCommitted :
  threshold (contextGate attendEvidence e0) ≡ stillDeliberating
oneRelevantPulseNotYetCommitted = refl

twoRelevantPulsesCommit :
  threshold (contextGate attendEvidence (contextGate attendEvidence e0)) ≡ committed
twoRelevantPulsesCommit = refl

irrelevantIdenticalPulseDoesNotAccumulate :
  contextGate ignoreEvidence e0 ≡ e0
irrelevantIdenticalPulseDoesNotAccumulate = refl

sameStartingEvidenceContextChangesDecisionVariable :
  contextGate attendEvidence e0 ≡ contextGate ignoreEvidence e0 → ⊥
sameStartingEvidenceContextChangesDecisionVariable ()

accumulationIsNotCommitment :
  contextGate attendEvidence e0 ≡ e1
  × threshold e1 ≡ stillDeliberating
accumulationIsNotCommitment = refl , refl

record BoundedEvidenceBoundary : Set where
  constructor boundedEvidenceBoundary
  field
    momentaryEvidenceEqualsCommitment : Bool
    irrelevantEvidenceDeletedFromCarrier : Bool
    thresholdIsSemanticTruth : Bool

canonicalBoundedEvidenceBoundary : BoundedEvidenceBoundary
canonicalBoundedEvidenceBoundary =
  boundedEvidenceBoundary false false false
