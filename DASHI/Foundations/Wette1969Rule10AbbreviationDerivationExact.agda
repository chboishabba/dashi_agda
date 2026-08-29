module DASHI.Foundations.Wette1969Rule10AbbreviationDerivationExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 10: ABBREVIATION PRODUCER
--
-- Eduard Wette, 1969, DOI 10.1007/978-3-642-86745-3_9.
-- Printed p.145:
--   10.1  -> =̇ (Λ o u) u
--   10.2  x V1, =̇ (Λ v u) w -> =̇ (Λ (u v V1) u) (Λ V1 w)
--
-- In Wette's intended reading the abbreviation relator is syntactic.  These
-- rules recursively package a block of generalizers.  They are exactly the
-- producer family used by 9.1.5 premises 16,17,26; this module supplies the
-- historical rule bodies and proof-carrying selectors, not a semantic theorem
-- about quantified formula equivalence.
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

generalize : WordTerm → WordTerm → WordTerm
generalize binder body =
  Signature.binaryWordTerm Signature.generalizationFunctor refl binder body

rule10-1Address : Revision.HistoricalRuleAddress
rule10-1Address = Revision.historicalRuleAddress 10 0 1

rule10-2Address : Revision.HistoricalRuleAddress
rule10-2Address = Revision.historicalRuleAddress 10 0 2

rule10-1 : (body : WordTerm) → RuleBody.HistoricalRuleBody
rule10-1 body =
  RuleBody.historicalRuleBody
    rule10-1Address
    0
    []ᵥ
    (Judgment.abbreviates (generalize emptyWord body) body)

rule10-2 :
  (variable tuple body expanded : WordTerm) → RuleBody.HistoricalRuleBody
rule10-2 variable tuple body expanded =
  RuleBody.historicalRuleBody
    rule10-2Address
    2
    ( Judgment.naturalVariable variable
    ∷ᵥ Judgment.abbreviates (generalize tuple body) expanded
    ∷ᵥ []ᵥ )
    (Judgment.abbreviates
      (generalize (juxtapose tuple variable) body)
      (generalize variable expanded))

emptyPremisesHold :
  (context : Context) → (body : WordTerm) →
  Historical.PremisesHold Finite.finiteHistoricalContextSystem context (rule10-1 body)
emptyPremisesHold context body ()

selectRule101 :
  (context : Context) → (body : WordTerm) →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule101 context body =
  PCRA.selectedRuleApplication
    (rule10-1 body)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem context (rule10-1 body)
      (emptyPremisesHold context body))

rule102PremisesHold :
  (context : Context) → (variable tuple body expanded : WordTerm) →
  Judgment.naturalVariable variable Finite.∈Context context →
  Judgment.abbreviates (generalize tuple body) expanded Finite.∈Context context →
  Historical.PremisesHold Finite.finiteHistoricalContextSystem context
    (rule10-2 variable tuple body expanded)
rule102PremisesHold context variable tuple body expanded variableEvidence abbreviationEvidence
  Fin.zero = variableEvidence
rule102PremisesHold context variable tuple body expanded variableEvidence abbreviationEvidence
  (Fin.suc Fin.zero) = abbreviationEvidence

selectRule102 :
  (context : Context) → (variable tuple body expanded : WordTerm) →
  Judgment.naturalVariable variable Finite.∈Context context →
  Judgment.abbreviates (generalize tuple body) expanded Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule102 context variable tuple body expanded variableEvidence abbreviationEvidence =
  PCRA.selectedRuleApplication
    (rule10-2 variable tuple body expanded)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem context
      (rule10-2 variable tuple body expanded)
      (rule102PremisesHold
        context variable tuple body expanded variableEvidence abbreviationEvidence))

record Wette1969Rule10AbbreviationBoundary : Set where
  constructor wette1969Rule10AbbreviationBoundary
  field
    rules101And102NowLiteralHistoricalBodies : Bool
    rules101And102NowLiteralHistoricalBodiesIsTrue :
      rules101And102NowLiteralHistoricalBodies ≡ true
    blockGeneralizerAbbreviationsHaveHistoricalProducerSteps : Bool
    blockGeneralizerAbbreviationsHaveHistoricalProducerStepsIsTrue :
      blockGeneralizerAbbreviationsHaveHistoricalProducerSteps ≡ true
    abbreviationDerivabilityAlreadyMeansSemanticEquivalence : Bool
    abbreviationDerivabilityAlreadyMeansSemanticEquivalenceIsFalse :
      abbreviationDerivabilityAlreadyMeansSemanticEquivalence ≡ false

canonicalWette1969Rule10AbbreviationBoundary : Wette1969Rule10AbbreviationBoundary
canonicalWette1969Rule10AbbreviationBoundary =
  wette1969Rule10AbbreviationBoundary true refl true refl false refl
