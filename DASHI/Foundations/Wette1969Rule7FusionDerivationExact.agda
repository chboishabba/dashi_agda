module DASHI.Foundations.Wette1969Rule7FusionDerivationExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 7: FUSION / JUXTAPOSITION-RESULT PRODUCER
--
-- Eduard Wette, 1969, DOI 10.1007/978-3-642-86745-3_9.
-- Printed p.144:
--   7.1  u*k W U -> + U o U
--   7.2  *k V, + U1 U2 U -> + U1 (u U2 V) (u U V)
--
-- The p.148 interpretation identifies + W1 W2 W3 as the judgement that W3
-- fuses W1 with W2.  This module puts the two source rules on the historical
-- rule carrier and exposes proof-carrying selectors.
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

emptyWord : WordTerm
emptyWord = Signature.constantWordTerm Signature.emptyConstant

juxtapose : WordTerm → WordTerm → WordTerm
juxtapose left right =
  Signature.binaryWordTerm Signature.juxtapositionFunctor refl left right

rule7-1Address : Revision.HistoricalRuleAddress
rule7-1Address = Revision.historicalRuleAddress 7 0 1

rule7-2Address : Revision.HistoricalRuleAddress
rule7-2Address = Revision.historicalRuleAddress 7 0 2

rule7-1 : (arity tuple : WordTerm) → RuleBody.HistoricalRuleBody
rule7-1 arity tuple =
  RuleBody.historicalRuleBody
    rule7-1Address
    1
    (Judgment.termTuple arity tuple ∷ᵥ []ᵥ)
    (Judgment.juxtapositionResult tuple emptyWord tuple)

rule7-2 :
  (term left right result : WordTerm) → RuleBody.HistoricalRuleBody
rule7-2 term left right result =
  RuleBody.historicalRuleBody
    rule7-2Address
    2
    ( Judgment.naturalTerm term
    ∷ᵥ Judgment.juxtapositionResult left right result
    ∷ᵥ []ᵥ )
    (Judgment.juxtapositionResult
      left
      (juxtapose right term)
      (juxtapose result term))

rule71PremisesHold :
  (context : Context) → (arity tuple : WordTerm) →
  Judgment.termTuple arity tuple Finite.∈Context context →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem context (rule7-1 arity tuple)
rule71PremisesHold context arity tuple tupleEvidence Fin.zero = tupleEvidence

selectRule71 :
  (context : Context) → (arity tuple : WordTerm) →
  Judgment.termTuple arity tuple Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule71 context arity tuple tupleEvidence =
  PCRA.selectedRuleApplication
    (rule7-1 arity tuple)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem context (rule7-1 arity tuple)
      (rule71PremisesHold context arity tuple tupleEvidence))

rule72PremisesHold :
  (context : Context) → (term left right result : WordTerm) →
  Judgment.naturalTerm term Finite.∈Context context →
  Judgment.juxtapositionResult left right result Finite.∈Context context →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem context
    (rule7-2 term left right result)
rule72PremisesHold context term left right result termEvidence fusionEvidence Fin.zero =
  termEvidence
rule72PremisesHold context term left right result termEvidence fusionEvidence
  (Fin.suc Fin.zero) = fusionEvidence

selectRule72 :
  (context : Context) → (term left right result : WordTerm) →
  Judgment.naturalTerm term Finite.∈Context context →
  Judgment.juxtapositionResult left right result Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule72 context term left right result termEvidence fusionEvidence =
  PCRA.selectedRuleApplication
    (rule7-2 term left right result)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem context (rule7-2 term left right result)
      (rule72PremisesHold
        context term left right result termEvidence fusionEvidence))

record Wette1969Rule7FusionBoundary : Set where
  constructor wette1969Rule7FusionBoundary
  field
    rules71And72NowLiteralHistoricalBodies : Bool
    rules71And72NowLiteralHistoricalBodiesIsTrue :
      rules71And72NowLiteralHistoricalBodies ≡ true
    fusionCanBeBuiltByProofCarryingHistoricalSteps : Bool
    fusionCanBeBuiltByProofCarryingHistoricalStepsIsTrue :
      fusionCanBeBuiltByProofCarryingHistoricalSteps ≡ true
    fusionJudgementAlreadyProvesSemanticConcatenationEquality : Bool
    fusionJudgementAlreadyProvesSemanticConcatenationEqualityIsFalse :
      fusionJudgementAlreadyProvesSemanticConcatenationEquality ≡ false

canonicalWette1969Rule7FusionBoundary : Wette1969Rule7FusionBoundary
canonicalWette1969Rule7FusionBoundary =
  wette1969Rule7FusionBoundary true refl true refl false refl
