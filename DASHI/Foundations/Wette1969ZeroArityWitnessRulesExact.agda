module DASHI.Foundations.Wette1969ZeroArityWitnessRulesExact where

------------------------------------------------------------------------
-- WETTE 1969: MINIMAL HISTORICAL RULE SET FOR ONE ZERO-ARITY 9.1.5 WITNESS
--
-- Source loci: printed pp.144--145 and Zusatz pp.193--194.
-- This owner transcribes only the rule bodies needed by the concrete
-- zero-arity witness; it is not a replacement catalogue for the full calculus.
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

emptyWord : WordTerm
emptyWord = Signature.constantWordTerm Signature.emptyConstant

verumWord : WordTerm
verumWord = Signature.constantWordTerm Signature.verumConstant

falsumWord : WordTerm
falsumWord = Signature.constantWordTerm Signature.falsumConstant

successor : WordTerm → WordTerm
successor w = Signature.unaryWordTerm Signature.successorFunctor refl w

juxtapose : WordTerm → WordTerm → WordTerm
juxtapose u v = Signature.binaryWordTerm Signature.juxtapositionFunctor refl u v

implication : WordTerm → WordTerm → WordTerm
implication u v = Signature.binaryWordTerm Signature.implicationFunctor refl u v

conjunction : WordTerm → WordTerm → WordTerm
conjunction u v = Signature.binaryWordTerm Signature.conjunctionFunctor refl u v

------------------------------------------------------------------------
-- 0.1, 0.2, 1.1, 2.1, 6.1.
------------------------------------------------------------------------

rule01 : RuleBody.HistoricalRuleBody
rule01 = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 0 0 1) 0 []ᵥ (Judgment.naturalNumber zeroWord)

rule02 : WordTerm → RuleBody.HistoricalRuleBody
rule02 w = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 0 0 2) 1
  (Judgment.naturalNumber w ∷ᵥ []ᵥ)
  (Judgment.naturalNumber (successor w))

rule11 : WordTerm → RuleBody.HistoricalRuleBody
rule11 w = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 1 0 1) 1
  (Judgment.naturalNumber w ∷ᵥ []ᵥ)
  (Judgment.unequal zeroWord (successor w))

rule21 : RuleBody.HistoricalRuleBody
rule21 = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 2 0 1) 0 []ᵥ
  (Judgment.duplicates zeroWord zeroWord)

rule61 : RuleBody.HistoricalRuleBody
rule61 = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 6 0 1) 0 []ᵥ
  (Judgment.termTuple zeroWord emptyWord)

------------------------------------------------------------------------
-- 8.1.18,22,23: a predicate mark is fresh for o, verum, falsum.
------------------------------------------------------------------------

rule8118 : WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule8118 arity mark = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 8 1 18) 1
  (Judgment.predicateMarkArity arity mark ∷ᵥ []ᵥ)
  (Judgment.freeForSyntax mark emptyWord)

rule8122 : WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule8122 arity mark = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 8 1 22) 1
  (Judgment.predicateMarkArity arity mark ∷ᵥ []ᵥ)
  (Judgment.freeForSyntax mark verumWord)

rule8123 : WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule8123 arity mark = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 8 1 23) 1
  (Judgment.predicateMarkArity arity mark ∷ᵥ []ᵥ)
  (Judgment.freeForSyntax mark falsumWord)

------------------------------------------------------------------------
-- 9.1.2--4: primitive verum/falsum predicate schemata and marks as predicates.
------------------------------------------------------------------------

rule912 : WordTerm → RuleBody.HistoricalRuleBody
rule912 arity = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 9 1 2) 1
  (Judgment.naturalNumber arity ∷ᵥ []ᵥ)
  (Judgment.predicateSchema arity verumWord)

rule913 : WordTerm → RuleBody.HistoricalRuleBody
rule913 arity = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 9 1 3) 1
  (Judgment.naturalNumber arity ∷ᵥ []ᵥ)
  (Judgment.predicateSchema arity falsumWord)

rule914 : WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule914 arity mark = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 9 1 4) 1
  (Judgment.predicateMarkArity arity mark ∷ᵥ []ᵥ)
  (Judgment.predicateSchema arity mark)

------------------------------------------------------------------------
-- 9.2.0--3 and 9.4.1.
------------------------------------------------------------------------

rule920 : WordTerm → RuleBody.HistoricalRuleBody
rule920 body = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 9 2 0) 1
  (Judgment.assertionSchemaNoPredicateQuantification body ∷ᵥ []ᵥ)
  (Judgment.assertionSchema body)

rule921 : WordTerm → WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule921 arity tuple predicate = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 9 2 1) 2
  ( Judgment.termTuple arity tuple
  ∷ᵥ Judgment.predicateSchema arity predicate
  ∷ᵥ []ᵥ )
  (Judgment.assertionSchema (juxtapose predicate tuple))

rule922 : WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule922 left right = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 9 2 2) 2
  (Judgment.assertionSchema left ∷ᵥ Judgment.assertionSchema right ∷ᵥ []ᵥ)
  (Judgment.assertionSchema (implication left right))

rule923 : WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule923 left right = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 9 2 3) 2
  (Judgment.assertionSchema left ∷ᵥ Judgment.assertionSchema right ∷ᵥ []ᵥ)
  (Judgment.assertionSchema (conjunction left right))

rule941 : WordTerm → WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule941 arity tuple predicate = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 9 4 1) 2
  ( Judgment.termTuple arity tuple
  ∷ᵥ Judgment.predicateSchema arity predicate
  ∷ᵥ []ᵥ )
  (Judgment.assertionSchemaNoPredicateQuantification (juxtapose predicate tuple))

------------------------------------------------------------------------
-- 9.3.1, 9.3.3/4 and 9.3.11.
------------------------------------------------------------------------

rule931 : WordTerm → WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule931 u w v = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 9 3 1) 2
  (Judgment.implies u w ∷ᵥ Judgment.implies w v ∷ᵥ []ᵥ)
  (Judgment.implies u v)

rule933 : WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule933 u v = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 9 3 3) 2
  (Judgment.assertionSchema u ∷ᵥ Judgment.assertionSchema v ∷ᵥ []ᵥ)
  (Judgment.implies (conjunction u v) u)

rule934 : WordTerm → WordTerm → RuleBody.HistoricalRuleBody
rule934 u v = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 9 3 4) 2
  (Judgment.assertionSchema u ∷ᵥ Judgment.assertionSchema v ∷ᵥ []ᵥ)
  (Judgment.implies (conjunction u v) v)

-- Wette §1.63 identifies 9.3.11 as ex falso quodlibet.
rule9311 : WordTerm → RuleBody.HistoricalRuleBody
rule9311 u = RuleBody.historicalRuleBody
  (Revision.historicalRuleAddress 9 3 11) 1
  (Judgment.assertionSchema u ∷ᵥ []ᵥ)
  (Judgment.implies (juxtapose falsumWord emptyWord) u)

------------------------------------------------------------------------
-- Proof-carrying selectors.
------------------------------------------------------------------------

select0 : (context : Context) → (rule : RuleBody.HistoricalRuleBody) →
  RuleBody.premiseCount rule ≡ 0 →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem) context
select0 context rule refl = PCRA.selectedRuleApplication rule
  (Historical.certifyHistoricalRule Finite.finiteHistoricalContextSystem context rule empty)
  where
    empty : Historical.PremisesHold Finite.finiteHistoricalContextSystem context rule
    empty ()

select1 : (context : Context) → (rule : RuleBody.HistoricalRuleBody) →
  (premise : Signature.Formula) →
  RuleBody.premises rule ≡ premise ∷ᵥ []ᵥ →
  premise Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem) context
select1 context rule premise refl evidence = PCRA.selectedRuleApplication rule
  (Historical.certifyHistoricalRule Finite.finiteHistoricalContextSystem context rule holds)
  where
    holds : Historical.PremisesHold Finite.finiteHistoricalContextSystem context rule
    holds Fin.zero = evidence

select2 : (context : Context) → (rule : RuleBody.HistoricalRuleBody) →
  (p q : Signature.Formula) →
  RuleBody.premises rule ≡ p ∷ᵥ q ∷ᵥ []ᵥ →
  p Finite.∈Context context → q Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem) context
select2 context rule p q refl pe qe = PCRA.selectedRuleApplication rule
  (Historical.certifyHistoricalRule Finite.finiteHistoricalContextSystem context rule holds)
  where
    holds : Historical.PremisesHold Finite.finiteHistoricalContextSystem context rule
    holds Fin.zero = pe
    holds (Fin.suc Fin.zero) = qe

record Wette1969ZeroArityWitnessRulesBoundary : Set where
  constructor wette1969ZeroArityWitnessRulesBoundary
  field
    minimalRuleBodiesTranscribedFromPrimaryRuleTables : Bool
    minimalRuleBodiesTranscribedFromPrimaryRuleTablesIsTrue : minimalRuleBodiesTranscribedFromPrimaryRuleTables ≡ true
    modifiedP193Rule941And920Included : Bool
    modifiedP193Rule941And920IncludedIsTrue : modifiedP193Rule941And920Included ≡ true
    rule9311EncodedAsSourceDeclaredExFalso : Bool
    rule9311EncodedAsSourceDeclaredExFalsoIsTrue : rule9311EncodedAsSourceDeclaredExFalso ≡ true
    ownerClaimsComplete97RuleCatalogue : Bool
    ownerClaimsComplete97RuleCatalogueIsFalse : ownerClaimsComplete97RuleCatalogue ≡ false

canonicalWette1969ZeroArityWitnessRulesBoundary : Wette1969ZeroArityWitnessRulesBoundary
canonicalWette1969ZeroArityWitnessRulesBoundary =
  wette1969ZeroArityWitnessRulesBoundary true refl true refl true refl false refl
