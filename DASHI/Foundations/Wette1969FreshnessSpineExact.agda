module DASHI.Foundations.Wette1969FreshnessSpineExact where

------------------------------------------------------------------------
-- WETTE 1969 J-FRESHNESS SPINE
--
-- Primary source: p.144 rule table and §1.62, DOI
-- 10.1007/978-3-642-86745-3_9.
--
-- This supplements the already reconstructed 8.1.12/13 and 8.1.17 rules with
-- the source's right-composition rule [8.1.0] and projection rules 8.1.14/15.
-- Together they provide the structural machinery needed to build compound J
-- side conditions from explicit atomic freshness receipts without pretending
-- freshness holds for arbitrary colliding words.
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

juxtapose : WordTerm → WordTerm → WordTerm
juxtapose left right =
  Signature.binaryWordTerm Signature.juxtapositionFunctor refl left right

rule8-1-0Address : Revision.HistoricalRuleAddress
rule8-1-0Address = Revision.historicalRuleAddress 8 1 0

rule8-1-14Address : Revision.HistoricalRuleAddress
rule8-1-14Address = Revision.historicalRuleAddress 8 1 14

rule8-1-15Address : Revision.HistoricalRuleAddress
rule8-1-15Address = Revision.historicalRuleAddress 8 1 15

rule8-1-0 : (excluded left right : WordTerm) → RuleBody.HistoricalRuleBody
rule8-1-0 excluded left right =
  RuleBody.historicalRuleBody
    rule8-1-0Address
    2
    ( Judgment.freeForSyntax excluded left
    ∷ᵥ Judgment.freeForSyntax excluded right
    ∷ᵥ []ᵥ )
    (Judgment.freeForSyntax excluded (juxtapose left right))

rule8-1-14 : (excluded left right : WordTerm) → RuleBody.HistoricalRuleBody
rule8-1-14 excluded left right =
  RuleBody.historicalRuleBody
    rule8-1-14Address
    1
    (Judgment.freeForSyntax excluded (juxtapose left right) ∷ᵥ []ᵥ)
    (Judgment.freeForSyntax excluded left)

rule8-1-15 : (excluded left right : WordTerm) → RuleBody.HistoricalRuleBody
rule8-1-15 excluded left right =
  RuleBody.historicalRuleBody
    rule8-1-15Address
    1
    (Judgment.freeForSyntax excluded (juxtapose left right) ∷ᵥ []ᵥ)
    (Judgment.freeForSyntax excluded right)

rule810PremisesHold :
  (context : Context) → (excluded left right : WordTerm) →
  Judgment.freeForSyntax excluded left Finite.∈Context context →
  Judgment.freeForSyntax excluded right Finite.∈Context context →
  Historical.PremisesHold Finite.finiteHistoricalContextSystem context
    (rule8-1-0 excluded left right)
rule810PremisesHold context excluded left right leftEvidence rightEvidence Fin.zero =
  leftEvidence
rule810PremisesHold context excluded left right leftEvidence rightEvidence
  (Fin.suc Fin.zero) = rightEvidence

selectRule810 :
  (context : Context) → (excluded left right : WordTerm) →
  Judgment.freeForSyntax excluded left Finite.∈Context context →
  Judgment.freeForSyntax excluded right Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule810 context excluded left right leftEvidence rightEvidence =
  PCRA.selectedRuleApplication
    (rule8-1-0 excluded left right)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem context
      (rule8-1-0 excluded left right)
      (rule810PremisesHold context excluded left right leftEvidence rightEvidence))

rule8114PremisesHold :
  (context : Context) → (excluded left right : WordTerm) →
  Judgment.freeForSyntax excluded (juxtapose left right) Finite.∈Context context →
  Historical.PremisesHold Finite.finiteHistoricalContextSystem context
    (rule8-1-14 excluded left right)
rule8114PremisesHold context excluded left right evidence Fin.zero = evidence

rule8115PremisesHold :
  (context : Context) → (excluded left right : WordTerm) →
  Judgment.freeForSyntax excluded (juxtapose left right) Finite.∈Context context →
  Historical.PremisesHold Finite.finiteHistoricalContextSystem context
    (rule8-1-15 excluded left right)
rule8115PremisesHold context excluded left right evidence Fin.zero = evidence

selectRule8114 :
  (context : Context) → (excluded left right : WordTerm) →
  Judgment.freeForSyntax excluded (juxtapose left right) Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule8114 context excluded left right evidence =
  PCRA.selectedRuleApplication
    (rule8-1-14 excluded left right)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem context
      (rule8-1-14 excluded left right)
      (rule8114PremisesHold context excluded left right evidence))

selectRule8115 :
  (context : Context) → (excluded left right : WordTerm) →
  Judgment.freeForSyntax excluded (juxtapose left right) Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule8115 context excluded left right evidence =
  PCRA.selectedRuleApplication
    (rule8-1-15 excluded left right)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem context
      (rule8-1-15 excluded left right)
      (rule8115PremisesHold context excluded left right evidence))

record Wette1969FreshnessSpineBoundary : Set where
  constructor wette1969FreshnessSpineBoundary
  field
    rightCompositionRule810NowLiteral : Bool
    rightCompositionRule810NowLiteralIsTrue : rightCompositionRule810NowLiteral ≡ true
    projectionRules8114And8115NowLiteral : Bool
    projectionRules8114And8115NowLiteralIsTrue : projectionRules8114And8115NowLiteral ≡ true
    compoundFreshnessCanBeHistoricallyBuiltFromAtomicReceipts : Bool
    compoundFreshnessCanBeHistoricallyBuiltFromAtomicReceiptsIsTrue :
      compoundFreshnessCanBeHistoricallyBuiltFromAtomicReceipts ≡ true
    freshnessForArbitraryWordsIsNotManufactured : Bool
    freshnessForArbitraryWordsIsNotManufacturedIsTrue :
      freshnessForArbitraryWordsIsNotManufactured ≡ true

canonicalWette1969FreshnessSpineBoundary : Wette1969FreshnessSpineBoundary
canonicalWette1969FreshnessSpineBoundary =
  wette1969FreshnessSpineBoundary true refl true refl true refl true refl
