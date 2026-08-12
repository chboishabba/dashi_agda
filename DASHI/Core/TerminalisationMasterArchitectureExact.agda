module DASHI.Core.TerminalisationMasterArchitectureExact where

------------------------------------------------------------------------
-- FOUR-PART MASTER ARCHITECTURE
--
-- 1. causal noncommutation is carried by an explicit constructive witness;
-- 2. classification does not promote identity/global proposition truth;
-- 3. protected provenance survives declared reopening;
-- 4. anti-terminalisation requires a corrective reopening path.
--
-- The record packages these obligations without asserting that every concrete
-- system satisfies them.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)

import DASHI.Core.TerminalisationArchitectureExact as TA
import DASHI.Core.SelfSealingTerminalisationExact as ST
import DASHI.Core.PropositionIndependenceExact as PI

record CausalProjectionDefect
    (History Coarse Cause : Set)
    (project : History → Coarse)
    (causeFine : History → Cause)
    (causeCoarse : Coarse → Cause) : Set₁ where
  constructor causalProjectionDefect
  field
    history : History
    noncommuting : causeCoarse (project history) ≡ causeFine history → ⊥

open CausalProjectionDefect public

record HealthyCompressionArchitecture : Set₁ where
  constructor healthyCompressionArchitecture
  field
    State Surface Receipt Critical : Set
    project : State → Surface
    critical : State → Critical
    protectedRecovery :
      TA.ProtectedProvenanceRecovery State Surface Receipt Critical project critical

open HealthyCompressionArchitecture public

record AntiTerminalisationArchitecture : Set₁ where
  constructor antiTerminalisationArchitecture
  field
    Class Evidence : Set
    update : Class → Evidence → Class
    Terminal : Class → Set
    correctiveReopening : ST.CorrectiveReopeningWitness Class Evidence update Terminal

open AntiTerminalisationArchitecture public

------------------------------------------------------------------------
-- Classification/local assessment authority remains non-promoting.
------------------------------------------------------------------------

masterLocalAssessmentCannotSettleAll :
  PI.GlobalVerdictFromLocal PI.localAssessmentOnly → ⊥
masterLocalAssessmentCannotSettleAll = PI.localAssessmentCannotSettleAll

------------------------------------------------------------------------
-- If a terminal region is closed under every evidence update, it is
-- incompatible with the anti-terminalisation witness by construction.
------------------------------------------------------------------------

closedTerminalRegionContradictsAntiTerminalisation :
  ∀ {Class Evidence}
    {update : Class → Evidence → Class}
    {Terminal : Class → Set} →
  ST.CounterevidenceClosure Class Evidence update Terminal →
  ST.CorrectiveReopeningWitness Class Evidence update Terminal →
  ⊥
closedTerminalRegionContradictsAntiTerminalisation =
  ST.selfSealingContradictsCorrectiveReopening
