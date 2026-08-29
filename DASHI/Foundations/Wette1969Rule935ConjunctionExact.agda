module DASHI.Foundations.Wette1969Rule935ConjunctionExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.3.5
-- Printed p.145:
--
--   L W U , L W V  ->  L W (U ∧ V)
--
-- This is the exact same-antecedent conjunction constructor needed by the
-- premise-27 independence branch after its two directional implications have
-- been produced.
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

conjunctionWord : WordTerm → WordTerm → WordTerm
conjunctionWord left right =
  Signature.binaryWordTerm Signature.conjunctionFunctor refl left right

rule9-3-5Address : Revision.HistoricalRuleAddress
rule9-3-5Address = Revision.historicalRuleAddress 9 3 5

rule9-3-5 : WordTerm → WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule9-3-5 antecedent left right =
  RuleBody.historicalRuleBody
    rule9-3-5Address
    2
    ( Judgment.implies antecedent left
    ∷ᵥ Judgment.implies antecedent right
    ∷ᵥ []ᵥ )
    (Judgment.implies antecedent (conjunctionWord left right))

rule935PremisesHold :
  (context : Context) →
  (antecedent left right : WordTerm) →
  Judgment.implies antecedent left Finite.∈Context context →
  Judgment.implies antecedent right Finite.∈Context context →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem context
    (rule9-3-5 antecedent left right)
rule935PremisesHold context antecedent left right leftEvidence rightEvidence Fin.zero =
  leftEvidence
rule935PremisesHold context antecedent left right leftEvidence rightEvidence
  (Fin.suc Fin.zero) = rightEvidence

selectRule935 :
  (context : Context) →
  (antecedent left right : WordTerm) →
  Judgment.implies antecedent left Finite.∈Context context →
  Judgment.implies antecedent right Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule935 context antecedent left right leftEvidence rightEvidence =
  PCRA.selectedRuleApplication
    (rule9-3-5 antecedent left right)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem context
      (rule9-3-5 antecedent left right)
      (rule935PremisesHold
        context antecedent left right leftEvidence rightEvidence))

record Wette1969Rule935ConjunctionBoundary : Set where
  constructor wette1969Rule935ConjunctionBoundary
  field
    rule935BodyTranscribedFromPrintedP145 : Bool
    rule935BodyTranscribedFromPrintedP145IsTrue :
      rule935BodyTranscribedFromPrintedP145 ≡ true
    rule935CombinesTwoSameAntecedentDirections : Bool
    rule935CombinesTwoSameAntecedentDirectionsIsTrue :
      rule935CombinesTwoSameAntecedentDirections ≡ true
    rule935ApplicationCarriesBothHistoricalPremiseReceipts : Bool
    rule935ApplicationCarriesBothHistoricalPremiseReceiptsIsTrue :
      rule935ApplicationCarriesBothHistoricalPremiseReceipts ≡ true

canonicalWette1969Rule935ConjunctionBoundary :
  Wette1969Rule935ConjunctionBoundary
canonicalWette1969Rule935ConjunctionBoundary =
  wette1969Rule935ConjunctionBoundary true refl true refl true refl
