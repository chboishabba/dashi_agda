module DASHI.Cognition.PNF.DecisionActionProjectionNonFactorabilityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Decision

------------------------------------------------------------------------
-- Same observed action, different fine decision state.
-- Reuses the generic non-factorability owner rather than introducing another
-- local theorem schema.
------------------------------------------------------------------------

data DecisionEpisode : Set where
  informedWithdrawal blockedCommitment unresolvedInaction : DecisionEpisode

data FineDecisionState : Set where
  informedState blockedCommittedState unresolvedState : FineDecisionState

observedAction : DecisionEpisode → Decision.ExecutedAction
observedAction informedWithdrawal = Decision.supportAction
observedAction blockedCommitment = Decision.noAction
observedAction unresolvedInaction = Decision.noAction

fineDecisionState : DecisionEpisode → FineDecisionState
fineDecisionState informedWithdrawal = informedState
fineDecisionState blockedCommitment = blockedCommittedState
fineDecisionState unresolvedInaction = unresolvedState

blockedAndUnresolvedShareAction :
  observedAction blockedCommitment ≡ observedAction unresolvedInaction
blockedAndUnresolvedShareAction = refl

blockedAndUnresolvedDifferFineState :
  fineDecisionState blockedCommitment ≡ fineDecisionState unresolvedInaction → ⊥
blockedAndUnresolvedDifferFineState ()

actionProjectionWitness :
  NF.NonFactorabilityWitness observedAction fineDecisionState
actionProjectionWitness =
  NF.nonFactorabilityWitness
    blockedCommitment
    unresolvedInaction
    refl
    blockedAndUnresolvedDifferFineState

actionCannotRecoverFineDecisionState :
  NF.FactorsThrough observedAction fineDecisionState → ⊥
actionCannotRecoverFineDecisionState =
  NF.witnessRulesOutEveryFlatFactorisation actionProjectionWitness
