module DASHI.Foundations.Wette1969Rule8112FreshnessDerivationExact where

------------------------------------------------------------------------
-- WETTE 1969 RULES 8.1.12/13: TUPLE-FRESHNESS DERIVATION
--
-- Eduard Wette, 1969, DOI 10.1007/978-3-642-86745-3_9.
--
-- Printed p.144 gives:
--   8.1.12  J v u, J w u -> J (u v w) u
--   8.1.13  -> J o u
--
-- Section 1.62 says these rules extend freshness from variables to variable
-- tuples.  This is exactly the producer needed for 9.3.24/25 premise 3: the
-- tuple-level freshness judgement is derived from component freshness rather
-- than imported as a single opaque premise.
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

rule8-1-12Address : Revision.HistoricalRuleAddress
rule8-1-12Address = Revision.historicalRuleAddress 8 1 12

rule8-1-13Address : Revision.HistoricalRuleAddress
rule8-1-13Address = Revision.historicalRuleAddress 8 1 13

rule8-1-12 :
  (left right contextWord : WordTerm) →
  RuleBody.HistoricalRuleBody
rule8-1-12 left right contextWord =
  RuleBody.historicalRuleBody
    rule8-1-12Address
    2
    ( Judgment.freeForSyntax left contextWord
    ∷ᵥ Judgment.freeForSyntax right contextWord
    ∷ᵥ []ᵥ )
    (Judgment.freeForSyntax (juxtapose left right) contextWord)

rule8-1-13 :
  (contextWord : WordTerm) →
  RuleBody.HistoricalRuleBody
rule8-1-13 contextWord =
  RuleBody.historicalRuleBody
    rule8-1-13Address
    0
    []ᵥ
    (Judgment.freeForSyntax emptyWord contextWord)

rule8112ComposesFreshness :
  (left right contextWord : WordTerm) →
  RuleBody.conclusion (rule8-1-12 left right contextWord)
    ≡ Judgment.freeForSyntax (juxtapose left right) contextWord
rule8112ComposesFreshness left right contextWord = refl

rule8113StartsEmptyFreshness :
  (contextWord : WordTerm) →
  RuleBody.conclusion (rule8-1-13 contextWord)
    ≡ Judgment.freeForSyntax emptyWord contextWord
rule8113StartsEmptyFreshness contextWord = refl

emptyPremisesHold :
  (context : Context) →
  (contextWord : WordTerm) →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem
    context
    (rule8-1-13 contextWord)
emptyPremisesHold context contextWord ()

selectRule8113 :
  (context : Context) →
  (contextWord : WordTerm) →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule8113 context contextWord =
  PCRA.selectedRuleApplication
    (rule8-1-13 contextWord)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem
      context
      (rule8-1-13 contextWord)
      (emptyPremisesHold context contextWord))

rule8112PremisesHold :
  (context : Context) →
  (left right contextWord : WordTerm) →
  Judgment.freeForSyntax left contextWord Finite.∈Context context →
  Judgment.freeForSyntax right contextWord Finite.∈Context context →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem
    context
    (rule8-1-12 left right contextWord)
rule8112PremisesHold context left right contextWord leftEvidence rightEvidence
  Fin.zero = leftEvidence
rule8112PremisesHold context left right contextWord leftEvidence rightEvidence
  (Fin.suc Fin.zero) = rightEvidence

selectRule8112 :
  (context : Context) →
  (left right contextWord : WordTerm) →
  Judgment.freeForSyntax left contextWord Finite.∈Context context →
  Judgment.freeForSyntax right contextWord Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule8112 context left right contextWord leftEvidence rightEvidence =
  PCRA.selectedRuleApplication
    (rule8-1-12 left right contextWord)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem
      context
      (rule8-1-12 left right contextWord)
      (rule8112PremisesHold
        context left right contextWord leftEvidence rightEvidence))

record Wette1969Rule8112FreshnessBoundary : Set where
  constructor wette1969Rule8112FreshnessBoundary
  field
    rules8112And8113NowLiteralHistoricalBodies : Bool
    rules8112And8113NowLiteralHistoricalBodiesIsTrue :
      rules8112And8113NowLiteralHistoricalBodies ≡ true

    tupleFreshnessCanBeGeneratedFromComponentFreshness : Bool
    tupleFreshnessCanBeGeneratedFromComponentFreshnessIsTrue :
      tupleFreshnessCanBeGeneratedFromComponentFreshness ≡ true

    emptyTupleFreshnessHasZeroPremiseProducer : Bool
    emptyTupleFreshnessHasZeroPremiseProducerIsTrue :
      emptyTupleFreshnessHasZeroPremiseProducer ≡ true

    componentFreshnessItselfIsAutomaticallyDerivableForEveryWord : Bool
    componentFreshnessItselfIsAutomaticallyDerivableForEveryWordIsFalse :
      componentFreshnessItselfIsAutomaticallyDerivableForEveryWord ≡ false

canonicalWette1969Rule8112FreshnessBoundary : Wette1969Rule8112FreshnessBoundary
canonicalWette1969Rule8112FreshnessBoundary =
  wette1969Rule8112FreshnessBoundary
    true refl
    true refl
    true refl
    false refl
