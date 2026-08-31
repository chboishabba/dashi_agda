module DASHI.Cognition.PNF.DecisionConflictAuditSeparationExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Cognition.PNF.AccessibleCandidateReasoningPipelineExact as Pre
import DASHI.Reasoning.FallacyObstructionCatalogue as Fallacy

------------------------------------------------------------------------
-- RESPONSE CONFLICT != FORMAL / FALLACY AUDIT
--
-- Literature calibration:
-- Matthew M. Botvinick; Todd S. Braver; Deanna M. Barch; Cameron S. Carter;
-- Jonathan D. Cohen,
-- "Conflict Monitoring and Cognitive Control",
-- DOI 10.1037/0033-295X.108.3.624.
--
-- The biological literature motivates a distinct conflict-monitoring signal.
-- The exact finite theorem below is structural only: response competition is
-- not identified with a logical fallacy, and a formal obstruction is not
-- inferred from conflict magnitude.
------------------------------------------------------------------------

data ConflictLevel : Set where lowConflict highConflict : ConflictLevel

record AuditConflictState : Set where
  constructor auditConflictState
  field
    formalAudit : Pre.AuditStatus
    responseConflict : ConflictLevel

open AuditConflictState public

cleanLow : AuditConflictState
cleanLow = auditConflictState Pre.cleanAudit lowConflict

cleanHigh : AuditConflictState
cleanHigh = auditConflictState Pre.cleanAudit highConflict

obstructedHigh : AuditConflictState
obstructedHigh =
  auditConflictState
    (Pre.obstructedAudit Fallacy.missingPremiseSupport)
    highConflict

sameFormalAuditDifferentConflict :
  formalAudit cleanLow ≡ formalAudit cleanHigh
  × (responseConflict cleanLow ≡ responseConflict cleanHigh → ⊥)
sameFormalAuditDifferentConflict = refl , (λ ())

sameConflictDifferentFormalAudit :
  responseConflict cleanHigh ≡ responseConflict obstructedHigh
  × (formalAudit cleanHigh ≡ formalAudit obstructedHigh → ⊥)
sameConflictDifferentFormalAudit = refl , (λ ())

formalAuditCannotDetermineConflict :
  NF.FactorsThrough formalAudit responseConflict → ⊥
formalAuditCannotDetermineConflict =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      cleanLow cleanHigh refl (λ ()))

conflictCannotDetermineFormalAudit :
  NF.FactorsThrough responseConflict formalAudit → ⊥
conflictCannotDetermineFormalAudit =
  NF.witnessRulesOutEveryFlatFactorisation
    (NF.nonFactorabilityWitness
      cleanHigh obstructedHigh refl (λ ()))

record DecisionConflictAuditBoundary : Set where
  constructor decisionConflictAuditBoundary
  field
    highConflictImpliesFallacy : Bool
    formalObstructionImpliesHighConflict : Bool
    conflictMonitoringEqualsLogicalAudit : Bool

canonicalDecisionConflictAuditBoundary : DecisionConflictAuditBoundary
canonicalDecisionConflictAuditBoundary =
  decisionConflictAuditBoundary false false false
