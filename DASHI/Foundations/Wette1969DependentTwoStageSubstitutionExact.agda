module DASHI.Foundations.Wette1969DependentTwoStageSubstitutionExact where

------------------------------------------------------------------------
-- WETTE 1969 DEPENDENT TWO-STAGE SUBSTITUTION / FOUR-PLACE II WELD
--
-- Eduard Wette,
-- "Definition eines (relativ vollständigen) formalen Systems konstruktiver
-- Arithmetik", Foundations of Mathematics, Springer 1969, pp. 130--195.
-- DOI: 10.1007/978-3-642-86745-3_9
--
-- Source loci:
--   * printed p.144, rule 8.2.8: two sequential II judgements combine into one
--     paired/simultaneous II judgement;
--   * printed p.148: when II's substituend and substitute begin with a Juxtor
--     not belonging to a variable/mark, the unique result is obtained by the
--     corresponding substitutions in sequence;
--   * printed pp.152--153: simultaneous substitutions generally depend on
--     order, and confusion-freedom cannot be detached from substitution without
--     reference to the intermediate results;
--   * section 1.632: in 9.3.24/25 premise 4, first V3 is substituted for V2,
--     then the recursively defined predicate is substituted for W2.
--
-- This module is the B3 weld.  It does not invent a monolithic substitution
-- function.  The second capture-safety proof is indexed by the *actual result*
-- of the first stage, and rule 8.2.8 reconstructs Wette's four-place paired II
-- judgement from those two ordered stages.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody
import DASHI.Foundations.Wette1969RuleRevisionExact as Revision
import DASHI.Foundations.Wette1969QuantifierCaptureSafetyExact as Capture

WordTerm = Signature.WordTerm
Formula = Signature.Formula

juxtapose : WordTerm → WordTerm → WordTerm
juxtapose left right =
  Signature.binaryWordTerm Signature.juxtapositionFunctor refl left right

------------------------------------------------------------------------
-- First stage: V2 -> V3 in the source/definiens.
------------------------------------------------------------------------

record TupleSubstitutionStage : Set where
  constructor tupleSubstitutionStage
  field
    oldTuple : WordTerm
    newTuple : WordTerm
    source : WordTerm
    intermediate : WordTerm
    captureSafeAtSource :
      Capture.QuantifierCaptureSafe oldTuple newTuple source

open TupleSubstitutionStage public

firstStageII : TupleSubstitutionStage → Formula
firstStageII stage =
  Judgment.substitution
    (oldTuple stage)
    (source stage)
    (newTuple stage)
    (intermediate stage)

------------------------------------------------------------------------
-- Second stage: W2 -> recursive predicate in the actual first-stage result.
------------------------------------------------------------------------

record PredicateSubstitutionStage (first : TupleSubstitutionStage) : Set where
  constructor predicateSubstitutionStage
  field
    predicateMark : WordTerm
    recursivePredicate : WordTerm
    result : WordTerm
    captureSafeAtActualIntermediate :
      Capture.QuantifierCaptureSafe
        predicateMark
        recursivePredicate
        (intermediate first)

open PredicateSubstitutionStage public

secondStageII :
  (first : TupleSubstitutionStage) →
  PredicateSubstitutionStage first →
  Formula
secondStageII first second =
  Judgment.substitution
    (predicateMark second)
    (intermediate first)
    (recursivePredicate second)
    (result second)

record DependentTwoStageSubstitution : Set where
  constructor dependentTwoStageSubstitution
  field
    first : TupleSubstitutionStage
    second : PredicateSubstitutionStage first

open DependentTwoStageSubstitution public

------------------------------------------------------------------------
-- Wette's special paired four-place II surface.
--
-- Rule 8.2.8 and p.148 pair the substituends as u(V2,W2) and the substitutes
-- as u(V3,R).  The p.148 convention interprets this four-place II by performing
-- the first component substitution and then the second.  Section 1.632 fixes
-- these components for 9.3.24/25 exactly as V2->V3 followed by W2->R.
------------------------------------------------------------------------

pairedSubstituend : DependentTwoStageSubstitution → WordTerm
pairedSubstituend stages =
  juxtapose
    (oldTuple (first stages))
    (predicateMark (second stages))

pairedReplacement : DependentTwoStageSubstitution → WordTerm
pairedReplacement stages =
  juxtapose
    (newTuple (first stages))
    (recursivePredicate (second stages))

pairedII : DependentTwoStageSubstitution → Formula
pairedII stages =
  Judgment.substitution
    (pairedSubstituend stages)
    (source (first stages))
    (pairedReplacement stages)
    (result (second stages))

------------------------------------------------------------------------
-- Literal source-level rule 8.2.8 composition schema.
------------------------------------------------------------------------

rule8-2-8Address : Revision.HistoricalRuleAddress
rule8-2-8Address = Revision.historicalRuleAddress 8 2 8

rule8-2-8Premises :
  (stages : DependentTwoStageSubstitution) → Vec Formula 2
rule8-2-8Premises stages =
  firstStageII (first stages) ∷ᵥ
  secondStageII (first stages) (second stages) ∷ᵥ
  []ᵥ

rule8-2-8 :
  DependentTwoStageSubstitution → RuleBody.HistoricalRuleBody
rule8-2-8 stages =
  RuleBody.historicalRuleBody
    rule8-2-8Address
    2
    (rule8-2-8Premises stages)
    (pairedII stages)

rule828HasTwoPremises :
  (stages : DependentTwoStageSubstitution) →
  RuleBody.premiseCount (rule8-2-8 stages) ≡ 2
rule828HasTwoPremises stages = refl

rule828ConcludesFourPlacePairedII :
  (stages : DependentTwoStageSubstitution) →
  RuleBody.conclusion (rule8-2-8 stages) ≡ pairedII stages
rule828ConcludesFourPlacePairedII stages = refl

secondStageSafetyReallyUsesFirstStageResult :
  (stages : DependentTwoStageSubstitution) →
  Capture.QuantifierCaptureSafe
    (predicateMark (second stages))
    (recursivePredicate (second stages))
    (intermediate (first stages))
secondStageSafetyReallyUsesFirstStageResult stages =
  captureSafeAtActualIntermediate (second stages)

pairedIIHasHistoricalSubstitutionRelator :
  (stages : DependentTwoStageSubstitution) →
  Signature.relator (pairedII stages) ≡ Signature.substitutionRelator
pairedIIHasHistoricalSubstitutionRelator stages = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record Wette1969DependentTwoStageSubstitutionBoundary : Set where
  constructor wette1969DependentTwoStageSubstitutionBoundary
  field
    secondStageSafetyIndexedByActualIntermediate : Bool
    secondStageSafetyIndexedByActualIntermediateIsTrue :
      secondStageSafetyIndexedByActualIntermediate ≡ true

    rule828SequentialCompositionNowTyped : Bool
    rule828SequentialCompositionNowTypedIsTrue :
      rule828SequentialCompositionNowTyped ≡ true

    pairedFourPlaceIIJudgementNowReproduced : Bool
    pairedFourPlaceIIJudgementNowReproducedIsTrue :
      pairedFourPlaceIIJudgementNowReproduced ≡ true

    sourceOrderV2ToV3ThenW2ToRecursivePredicatePreserved : Bool
    sourceOrderV2ToV3ThenW2ToRecursivePredicatePreservedIsTrue :
      sourceOrderV2ToV3ThenW2ToRecursivePredicatePreserved ≡ true

    captureSafetyCheckedOnlyOnceBeforeBothStages : Bool
    captureSafetyCheckedOnlyOnceBeforeBothStagesIsFalse :
      captureSafetyCheckedOnlyOnceBeforeBothStages ≡ false

    typedIIFormulaIsAlreadyHistoricalDerivabilityProof : Bool
    typedIIFormulaIsAlreadyHistoricalDerivabilityProofIsFalse :
      typedIIFormulaIsAlreadyHistoricalDerivabilityProof ≡ false

    quantifierFragmentAlreadyCoversEveryRecursorCaptureCase : Bool
    quantifierFragmentAlreadyCoversEveryRecursorCaptureCaseIsFalse :
      quantifierFragmentAlreadyCoversEveryRecursorCaptureCase ≡ false

canonicalWette1969DependentTwoStageSubstitutionBoundary :
  Wette1969DependentTwoStageSubstitutionBoundary
canonicalWette1969DependentTwoStageSubstitutionBoundary =
  wette1969DependentTwoStageSubstitutionBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
