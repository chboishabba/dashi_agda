module DASHI.Core.PropositionIndependenceExact where

------------------------------------------------------------------------
-- PROPOSITION INDEPENDENCE / NO GLOBAL CREDIBILITY PROMOTION
--
-- Distinct propositions have distinct truth/evidence coordinates.  A verdict
-- on one proposition carries no constructor that settles another proposition,
-- and a process/diagnosis coordinate is typed separately from proposition
-- truth.  This is a type-level non-promotion boundary, not an empirical claim.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data TruthStatus : Set where
  supported refuted unresolved : TruthStatus

data ProcessStatus : Set where
  ordinary altered unknown : ProcessStatus

record PropositionAssessment (Proposition Evidence : Set) : Set₁ where
  constructor propositionAssessment
  field
    proposition : Proposition
    evidence : Evidence
    status : TruthStatus

open PropositionAssessment public

record IndependentAssessmentPair
    (P Q EvidenceP EvidenceQ : Set) : Set₁ where
  constructor independentAssessmentPair
  field
    left : PropositionAssessment P EvidenceP
    right : PropositionAssessment Q EvidenceQ

open IndependentAssessmentPair public

------------------------------------------------------------------------
-- There is deliberately no constructor from a left verdict to a right verdict.
------------------------------------------------------------------------

data CrossPropositionAuthority : Set where
  localAssessmentOnly : CrossPropositionAuthority

data GlobalVerdictFromLocal : CrossPropositionAuthority → Set where

localAssessmentCannotSettleAll : GlobalVerdictFromLocal localAssessmentOnly → ⊥
localAssessmentCannotSettleAll ()

------------------------------------------------------------------------
-- Process state and proposition truth are orthogonal typed axes.
------------------------------------------------------------------------

record ProcessIndexedAssessment (Proposition Evidence : Set) : Set₁ where
  constructor processIndexedAssessment
  field
    process : ProcessStatus
    assessment : PropositionAssessment Proposition Evidence

open ProcessIndexedAssessment public

changeProcessPreservesAssessment :
  ∀ {Proposition Evidence}
    (newProcess : ProcessStatus)
    (state : ProcessIndexedAssessment Proposition Evidence) →
  assessment (processIndexedAssessment newProcess (assessment state)) ≡ assessment state
changeProcessPreservesAssessment newProcess state = refl
