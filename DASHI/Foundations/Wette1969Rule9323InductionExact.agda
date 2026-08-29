module DASHI.Foundations.Wette1969Rule9323InductionExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.3.23: COMPLETE-INDUCTION RULE BODY
--
-- Direct transcription of printed p.145:
--
--   x V, A U, II V U 'V U1, II V U 0 U2, L U U1  ->  L U2 U
--
-- In the intended reading discussed immediately after the rule table this is
-- Wette's complete-induction rule over natural-number variables.  The formal
-- owner below stays at the pure historical syntax: one natural-variable
-- premise, one assertion-schema premise, successor and zero substitution
-- receipts, and the induction-step L premise.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
import Data.Fin as Fin

import DASHI.Core.ProofCarryingRuleApplicationExact as PCRA
import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969RuleRevisionExact as Revision
import DASHI.Foundations.Wette1969ProofCarryingRuleApplicationExact as Historical
import DASHI.Foundations.Wette1969FiniteDerivationContextExact as Finite

WordTerm = Signature.WordTerm
Context = Finite.DerivationContext

zeroWord : WordTerm
zeroWord = Signature.constantWordTerm Signature.zeroConstant

successor : WordTerm → WordTerm
successor variable =
  Signature.unaryWordTerm Signature.successorFunctor refl variable

rule9-3-23Address : Revision.HistoricalRuleAddress
rule9-3-23Address = Revision.historicalRuleAddress 9 3 23

rule9-3-23 :
  (variable body successorInstance zeroInstance : WordTerm) →
  RuleBody.HistoricalRuleBody
rule9-3-23 variable body successorInstance zeroInstance =
  RuleBody.historicalRuleBody
    rule9-3-23Address
    5
    ( Judgment.naturalVariable variable
    ∷ᵥ Judgment.assertionSchema body
    ∷ᵥ Judgment.substitution variable body (successor variable) successorInstance
    ∷ᵥ Judgment.substitution variable body zeroWord zeroInstance
    ∷ᵥ Judgment.implies body successorInstance
    ∷ᵥ []ᵥ )
    (Judgment.implies zeroInstance body)

rule9323PremisesHold :
  (context : Context) →
  (variable body successorInstance zeroInstance : WordTerm) →
  Judgment.naturalVariable variable Finite.∈Context context →
  Judgment.assertionSchema body Finite.∈Context context →
  Judgment.substitution variable body (successor variable) successorInstance
    Finite.∈Context context →
  Judgment.substitution variable body zeroWord zeroInstance
    Finite.∈Context context →
  Judgment.implies body successorInstance Finite.∈Context context →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem context
    (rule9-3-23 variable body successorInstance zeroInstance)
rule9323PremisesHold context variable body successorInstance zeroInstance
  variableEvidence bodyEvidence successorEvidence zeroEvidence stepEvidence Fin.zero =
  variableEvidence
rule9323PremisesHold context variable body successorInstance zeroInstance
  variableEvidence bodyEvidence successorEvidence zeroEvidence stepEvidence
  (Fin.suc Fin.zero) = bodyEvidence
rule9323PremisesHold context variable body successorInstance zeroInstance
  variableEvidence bodyEvidence successorEvidence zeroEvidence stepEvidence
  (Fin.suc (Fin.suc Fin.zero)) = successorEvidence
rule9323PremisesHold context variable body successorInstance zeroInstance
  variableEvidence bodyEvidence successorEvidence zeroEvidence stepEvidence
  (Fin.suc (Fin.suc (Fin.suc Fin.zero))) = zeroEvidence
rule9323PremisesHold context variable body successorInstance zeroInstance
  variableEvidence bodyEvidence successorEvidence zeroEvidence stepEvidence
  (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = stepEvidence

selectRule9323 :
  (context : Context) →
  (variable body successorInstance zeroInstance : WordTerm) →
  Judgment.naturalVariable variable Finite.∈Context context →
  Judgment.assertionSchema body Finite.∈Context context →
  Judgment.substitution variable body (successor variable) successorInstance
    Finite.∈Context context →
  Judgment.substitution variable body zeroWord zeroInstance
    Finite.∈Context context →
  Judgment.implies body successorInstance Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule9323 context variable body successorInstance zeroInstance
  variableEvidence bodyEvidence successorEvidence zeroEvidence stepEvidence =
  PCRA.selectedRuleApplication
    (rule9-3-23 variable body successorInstance zeroInstance)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem context
      (rule9-3-23 variable body successorInstance zeroInstance)
      (rule9323PremisesHold
        context variable body successorInstance zeroInstance
        variableEvidence bodyEvidence successorEvidence zeroEvidence stepEvidence))

rule9323HasFivePremises :
  (variable body successorInstance zeroInstance : WordTerm) →
  RuleBody.premiseCount
    (rule9-3-23 variable body successorInstance zeroInstance) ≡ 5
rule9323HasFivePremises variable body successorInstance zeroInstance = refl

rule9323ConclusionIsBaseImpliesBody :
  (variable body successorInstance zeroInstance : WordTerm) →
  RuleBody.conclusion
    (rule9-3-23 variable body successorInstance zeroInstance)
    ≡ Judgment.implies zeroInstance body
rule9323ConclusionIsBaseImpliesBody variable body successorInstance zeroInstance = refl

record Wette1969Rule9323InductionBoundary : Set where
  constructor wette1969Rule9323InductionBoundary
  field
    rule9323BodyTranscribedFromPrintedP145 : Bool
    rule9323BodyTranscribedFromPrintedP145IsTrue :
      rule9323BodyTranscribedFromPrintedP145 ≡ true
    rule9323HasFiveHistoricalPremises : Bool
    rule9323HasFiveHistoricalPremisesIsTrue :
      rule9323HasFiveHistoricalPremises ≡ true
    successorAndZeroSubstitutionReceiptsRemainExplicit : Bool
    successorAndZeroSubstitutionReceiptsRemainExplicitIsTrue :
      successorAndZeroSubstitutionReceiptsRemainExplicit ≡ true
    inductionStepIsHistoricalLReceipt : Bool
    inductionStepIsHistoricalLReceiptIsTrue :
      inductionStepIsHistoricalLReceipt ≡ true
    rule9323AutomaticallyProvesArbitraryPredecessorInduction : Bool
    rule9323AutomaticallyProvesArbitraryPredecessorInductionIsFalse :
      rule9323AutomaticallyProvesArbitraryPredecessorInduction ≡ false

canonicalWette1969Rule9323InductionBoundary : Wette1969Rule9323InductionBoundary
canonicalWette1969Rule9323InductionBoundary =
  wette1969Rule9323InductionBoundary
    true refl true refl true refl true refl false refl
