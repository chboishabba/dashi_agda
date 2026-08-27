module DASHI.Biology.NeuralDecisionProducerBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Cognition.PNF.AccessibleCandidateReasoningPipelineExact as Pre
import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Decision
import DASHI.Cognition.PNF.FastAccessControlFieldExact as Access
import DASHI.Reasoning.AttractorAlignedBranchSelectionExact as Branch

------------------------------------------------------------------------
-- Literature calibration:
--
-- Valerio Mante, David Sussillo, Krishna V. Shenoy, William T. Newsome,
-- "Context-dependent computation by recurrent dynamics in prefrontal cortex",
-- DOI 10.1038/nature12742.
--
-- Xiao-Jing Wang,
-- "Probabilistic Decision Making by Slow Reverberation in Cortical Circuits",
-- DOI 10.1016/S0896-6273(02)01092-9.
--
-- Kong-Fatt Wong, Xiao-Jing Wang,
-- "A Recurrent Network Mechanism of Time Integration in Perceptual Decisions",
-- DOI 10.1523/JNEUROSCI.3733-05.2006.
--
-- These sources calibrate candidate neural producers.  They do not identify
-- one cortical region or circuit with DASHI's abstract decision semantics.
------------------------------------------------------------------------

data NeuralContext : Set where
  supportContext counterContext : NeuralContext

contextAccess : NeuralContext → Pre.Candidate → Bool
contextAccess supportContext Pre.supportingCandidate = true
contextAccess supportContext Pre.counterCandidate = false
contextAccess counterContext Pre.supportingCandidate = true
contextAccess counterContext Pre.counterCandidate = true

sameStoredCounterDifferentContextAccess :
  Pre.stored Pre.counterCandidate ≡ true
  × contextAccess supportContext Pre.counterCandidate ≡ false
  × contextAccess counterContext Pre.counterCandidate ≡ true
sameStoredCounterDifferentContextAccess = refl , (refl , refl)

------------------------------------------------------------------------
-- A minimal recurrent evidence producer feeding the generic accumulator.
------------------------------------------------------------------------

recurrentStep : NeuralContext → Decision.Accumulator → Decision.Accumulator
recurrentStep supportContext s = Decision.accumulate Pre.supportingCandidate s
recurrentStep counterContext s = Decision.accumulate Pre.counterCandidate s

supportContextBuildsSupportLead :
  recurrentStep supportContext Decision.balanced ≡ Decision.supportLead
supportContextBuildsSupportLead = refl

counterContextBuildsCounterLead :
  recurrentStep counterContext Decision.balanced ≡ Decision.counterLead
counterContextBuildsCounterLead = refl

contextCanChangeCommitment :
  Decision.commit (recurrentStep supportContext Decision.balanced)
  ≡
  Decision.commit (recurrentStep counterContext Decision.balanced) → ⊥
contextCanChangeCommitment ()

------------------------------------------------------------------------
-- Actuation gating remains downstream and independent of commitment.
------------------------------------------------------------------------

committedButBlocked :
  Decision.commit Decision.supportLead ≡ Decision.supportCommitted
  × Decision.actuate Decision.blocked Decision.supportCommitted ≡ Decision.noAction
committedButBlocked = refl , refl

sameCommitmentReleasedOrBlocked :
  Decision.actuate Decision.blocked Decision.counterCommitted
  ≡ Decision.actuate Decision.released Decision.counterCommitted → ⊥
sameCommitmentReleasedOrBlocked ()

------------------------------------------------------------------------
-- Existing attractor/branch owner supplies interaction semantics rather than
-- duplicating another winner-take-all ontology.
------------------------------------------------------------------------

recurrentAttractorBranchPolicy : Branch.AttractorAlignedPolicy
recurrentAttractorBranchPolicy = Branch.canonicalAttractorAlignedPolicy

record NeuralDecisionProducerBoundary : Set where
  constructor neuralDecisionProducerBoundary
  field
    contextDeletesStoredRepresentation : Bool
    recurrentAccumulatorEqualsSemanticTruth : Bool
    commitmentEqualsActuation : Bool
    oneCircuitDefinesDecision : Bool

canonicalNeuralDecisionProducerBoundary : NeuralDecisionProducerBoundary
canonicalNeuralDecisionProducerBoundary =
  neuralDecisionProducerBoundary false false false false
