module DASHI.Foundations.Wette1969Rule83TupleDerivationExact where

------------------------------------------------------------------------
-- WETTE 1969 RULES 8.3.1/2: DISTINCT VARIABLE-TUPLE DERIVATION
--
-- Eduard Wette, 1969, DOI 10.1007/978-3-642-86745-3_9.
--
-- Printed p.144 gives:
--   8.3.1  -> u_x 0 o
--   8.3.2  x v, J v u, u_x w u -> u_x (' w) (u u v)
--
-- Section 1.61 explains the role exactly: 8.3 produces variable k-tuples whose
-- variables have pairwise different distinguishing indices.  This module puts
-- those two rules on the existing HistoricalRuleBody carrier and lifts them to
-- proof-carrying finite-context transitions.
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
Formula = Signature.Formula
Context = Finite.DerivationContext

emptyWord : WordTerm
emptyWord = Signature.constantWordTerm Signature.emptyConstant

zeroWord : WordTerm
zeroWord = Signature.constantWordTerm Signature.zeroConstant

successor : WordTerm → WordTerm
successor term =
  Signature.unaryWordTerm Signature.successorFunctor refl term

juxtapose : WordTerm → WordTerm → WordTerm
juxtapose left right =
  Signature.binaryWordTerm Signature.juxtapositionFunctor refl left right

rule8-3-1Address : Revision.HistoricalRuleAddress
rule8-3-1Address = Revision.historicalRuleAddress 8 3 1

rule8-3-2Address : Revision.HistoricalRuleAddress
rule8-3-2Address = Revision.historicalRuleAddress 8 3 2

rule8-3-1 : RuleBody.HistoricalRuleBody
rule8-3-1 =
  RuleBody.historicalRuleBody
    rule8-3-1Address
    0
    []ᵥ
    (Judgment.distinctVariableTuple zeroWord emptyWord)

rule8-3-2 :
  (arity tuple variable : WordTerm) →
  RuleBody.HistoricalRuleBody
rule8-3-2 arity tuple variable =
  RuleBody.historicalRuleBody
    rule8-3-2Address
    3
    ( Judgment.naturalVariable variable
    ∷ᵥ Judgment.freeForSyntax variable tuple
    ∷ᵥ Judgment.distinctVariableTuple arity tuple
    ∷ᵥ []ᵥ )
    (Judgment.distinctVariableTuple
      (successor arity)
      (juxtapose tuple variable))

rule831HasZeroPremises : RuleBody.premiseCount rule8-3-1 ≡ 0
rule831HasZeroPremises = refl

rule832HasThreePremises :
  (arity tuple variable : WordTerm) →
  RuleBody.premiseCount (rule8-3-2 arity tuple variable) ≡ 3
rule832HasThreePremises arity tuple variable = refl

rule831ProducesEmptyDistinctTuple :
  RuleBody.conclusion rule8-3-1
    ≡ Judgment.distinctVariableTuple zeroWord emptyWord
rule831ProducesEmptyDistinctTuple = refl

rule832ExtendsDistinctTupleByFreshVariable :
  (arity tuple variable : WordTerm) →
  RuleBody.conclusion (rule8-3-2 arity tuple variable)
    ≡ Judgment.distinctVariableTuple
        (successor arity)
        (juxtapose tuple variable)
rule832ExtendsDistinctTupleByFreshVariable arity tuple variable = refl

emptyPremisesHold :
  (context : Context) →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem context rule8-3-1
emptyPremisesHold context ()

selectRule831 :
  (context : Context) →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule831 context =
  PCRA.selectedRuleApplication
    rule8-3-1
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem
      context
      rule8-3-1
      (emptyPremisesHold context))

rule832PremisesHold :
  (context : Context) →
  (arity tuple variable : WordTerm) →
  Judgment.naturalVariable variable Finite.∈Context context →
  Judgment.freeForSyntax variable tuple Finite.∈Context context →
  Judgment.distinctVariableTuple arity tuple Finite.∈Context context →
  Historical.PremisesHold
    Finite.finiteHistoricalContextSystem
    context
    (rule8-3-2 arity tuple variable)
rule832PremisesHold context arity tuple variable variableEvidence freshnessEvidence tupleEvidence
  Fin.zero = variableEvidence
rule832PremisesHold context arity tuple variable variableEvidence freshnessEvidence tupleEvidence
  (Fin.suc Fin.zero) = freshnessEvidence
rule832PremisesHold context arity tuple variable variableEvidence freshnessEvidence tupleEvidence
  (Fin.suc (Fin.suc Fin.zero)) = tupleEvidence

selectRule832 :
  (context : Context) →
  (arity tuple variable : WordTerm) →
  Judgment.naturalVariable variable Finite.∈Context context →
  Judgment.freeForSyntax variable tuple Finite.∈Context context →
  Judgment.distinctVariableTuple arity tuple Finite.∈Context context →
  PCRA.SelectedRuleApplication
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
selectRule832 context arity tuple variable variableEvidence freshnessEvidence tupleEvidence =
  PCRA.selectedRuleApplication
    (rule8-3-2 arity tuple variable)
    (Historical.certifyHistoricalRule
      Finite.finiteHistoricalContextSystem
      context
      (rule8-3-2 arity tuple variable)
      (rule832PremisesHold
        context arity tuple variable
        variableEvidence freshnessEvidence tupleEvidence))

emptyTupleTrace :
  (context : Context) →
  PCRA.CertifiedRuleTrace
    (Historical.historicalRuleApplicationSystem Finite.finiteHistoricalContextSystem)
    context
emptyTupleTrace context =
  PCRA.choose (selectRule831 context) PCRA.done

record Wette1969Rule83TupleBoundary : Set where
  constructor wette1969Rule83TupleBoundary
  field
    rules831And832NowLiteralHistoricalBodies : Bool
    rules831And832NowLiteralHistoricalBodiesIsTrue :
      rules831And832NowLiteralHistoricalBodies ≡ true

    rule831StartsEmptyDistinctTuple : Bool
    rule831StartsEmptyDistinctTupleIsTrue :
      rule831StartsEmptyDistinctTuple ≡ true

    rule832ExtendsTupleUsingVariableAndFreshnessPremises : Bool
    rule832ExtendsTupleUsingVariableAndFreshnessPremisesIsTrue :
      rule832ExtendsTupleUsingVariableAndFreshnessPremises ≡ true

    tupleFormationNowHasProofCarryingHistoricalSteps : Bool
    tupleFormationNowHasProofCarryingHistoricalStepsIsTrue :
      tupleFormationNowHasProofCarryingHistoricalSteps ≡ true

    tupleWordShapeAloneProvesAllVariableSideConditions : Bool
    tupleWordShapeAloneProvesAllVariableSideConditionsIsFalse :
      tupleWordShapeAloneProvesAllVariableSideConditions ≡ false

canonicalWette1969Rule83TupleBoundary : Wette1969Rule83TupleBoundary
canonicalWette1969Rule83TupleBoundary =
  wette1969Rule83TupleBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
