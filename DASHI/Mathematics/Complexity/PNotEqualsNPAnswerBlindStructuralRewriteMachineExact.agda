module DASHI.Mathematics.Complexity.PNotEqualsNPAnswerBlindStructuralRewriteMachineExact where

------------------------------------------------------------------------
-- ANSWER-BLIND STRUCTURAL REWRITE MACHINE FOR Q1 REPRESENTATIVE CHAINS
--
-- The previous generated-Q1 owner still asks the constructor to provide a
-- StructuralRepresentativeChain for each strict representative.
--
-- This owner replaces opaque chain construction by a restricted syntax whose
-- only primitive steps are evaluator-valid Boolean identities:
--
--   not true       -> false
--   not false      -> true
--   not (not p)    -> p
--   true and p     -> p
--   p and true     -> p
--   false and p    -> false
--   p and false    -> false
--   false or p     -> p
--   p or false     -> p
--   true or p      -> true
--   p or true      -> true
--
-- The relation is context closed under negate / conjunction / disjunction.
--
-- Every constructor is proved:
--   * pointwise evaluation preserving;
--   * satisfiability preserving;
--   * strictly node-count decreasing.
--
-- A RewriteProgram ends only at a literal constant.  Compiling it produces the
-- existing StructuralRepresentativeChain with no SAT-decider call and no
-- opaque equisatisfiability certificate supplied by the program.
--
-- IMPORTANT: this pays the CHAIN EXECUTION LANGUAGE.  It does not prove that
-- every Q1 representative admits such a program.  Failure to normalize exposes
-- the exact additional structural rewrite principle still needed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as NatP
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as Size
import DASHI.Mathematics.Complexity.PNotEqualsNPStrictSemanticRepresentativeQuotientExact as Strict
import DASHI.Mathematics.Complexity.PNotEqualsNPClosedStrictRepresentativeQuotientExact as Closed

------------------------------------------------------------------------
-- Restricted rewrite syntax.
------------------------------------------------------------------------

data StructuralRewrite :
    Cook.BooleanFormula →
    Cook.BooleanFormula →
    Set where

  negateTrue :
    StructuralRewrite
      (Cook.negate (Cook.constant true))
      (Cook.constant false)

  negateFalse :
    StructuralRewrite
      (Cook.negate (Cook.constant false))
      (Cook.constant true)

  doubleNegation :
    (formula : Cook.BooleanFormula) →
    StructuralRewrite
      (Cook.negate (Cook.negate formula))
      formula

  andTrueLeft :
    (formula : Cook.BooleanFormula) →
    StructuralRewrite
      (Cook.conjunction (Cook.constant true) formula)
      formula

  andTrueRight :
    (formula : Cook.BooleanFormula) →
    StructuralRewrite
      (Cook.conjunction formula (Cook.constant true))
      formula

  andFalseLeft :
    (formula : Cook.BooleanFormula) →
    StructuralRewrite
      (Cook.conjunction (Cook.constant false) formula)
      (Cook.constant false)

  andFalseRight :
    (formula : Cook.BooleanFormula) →
    StructuralRewrite
      (Cook.conjunction formula (Cook.constant false))
      (Cook.constant false)

  orFalseLeft :
    (formula : Cook.BooleanFormula) →
    StructuralRewrite
      (Cook.disjunction (Cook.constant false) formula)
      formula

  orFalseRight :
    (formula : Cook.BooleanFormula) →
    StructuralRewrite
      (Cook.disjunction formula (Cook.constant false))
      formula

  orTrueLeft :
    (formula : Cook.BooleanFormula) →
    StructuralRewrite
      (Cook.disjunction (Cook.constant true) formula)
      (Cook.constant true)

  orTrueRight :
    (formula : Cook.BooleanFormula) →
    StructuralRewrite
      (Cook.disjunction formula (Cook.constant true))
      (Cook.constant true)

  underNegate :
    ∀ {before after} →
    StructuralRewrite before after →
    StructuralRewrite
      (Cook.negate before)
      (Cook.negate after)

  underConjunctionLeft :
    ∀ {before after} →
    (right : Cook.BooleanFormula) →
    StructuralRewrite before after →
    StructuralRewrite
      (Cook.conjunction before right)
      (Cook.conjunction after right)

  underConjunctionRight :
    ∀ {before after} →
    (left : Cook.BooleanFormula) →
    StructuralRewrite before after →
    StructuralRewrite
      (Cook.conjunction left before)
      (Cook.conjunction left after)

  underDisjunctionLeft :
    ∀ {before after} →
    (right : Cook.BooleanFormula) →
    StructuralRewrite before after →
    StructuralRewrite
      (Cook.disjunction before right)
      (Cook.disjunction after right)

  underDisjunctionRight :
    ∀ {before after} →
    (left : Cook.BooleanFormula) →
    StructuralRewrite before after →
    StructuralRewrite
      (Cook.disjunction left before)
      (Cook.disjunction left after)

------------------------------------------------------------------------
-- Pointwise evaluator equality.
------------------------------------------------------------------------

rewriteEvaluationExact :
  ∀ {before after} →
  StructuralRewrite before after →
  (assignment : Cook.Assignment) →
  Cook.evaluate before assignment
  ≡
  Cook.evaluate after assignment

rewriteEvaluationExact negateTrue assignment =
  refl
rewriteEvaluationExact negateFalse assignment =
  refl

rewriteEvaluationExact (doubleNegation formula) assignment
    with Cook.evaluate formula assignment
... | false = refl
... | true = refl

rewriteEvaluationExact (andTrueLeft formula) assignment =
  refl

rewriteEvaluationExact (andTrueRight formula) assignment
    with Cook.evaluate formula assignment
... | false = refl
... | true = refl

rewriteEvaluationExact (andFalseLeft formula) assignment =
  refl

rewriteEvaluationExact (andFalseRight formula) assignment
    with Cook.evaluate formula assignment
... | false = refl
... | true = refl

rewriteEvaluationExact (orFalseLeft formula) assignment =
  refl

rewriteEvaluationExact (orFalseRight formula) assignment
    with Cook.evaluate formula assignment
... | false = refl
... | true = refl

rewriteEvaluationExact (orTrueLeft formula) assignment =
  refl

rewriteEvaluationExact (orTrueRight formula) assignment
    with Cook.evaluate formula assignment
... | false = refl
... | true = refl

rewriteEvaluationExact (underNegate rewrite) assignment =
  cong
    Cook.notBool
    (rewriteEvaluationExact rewrite assignment)

rewriteEvaluationExact
    (underConjunctionLeft right rewrite)
    assignment =
  cong
    (λ bit →
      Cook.andBool bit
        (Cook.evaluate right assignment))
    (rewriteEvaluationExact rewrite assignment)

rewriteEvaluationExact
    (underConjunctionRight left rewrite)
    assignment =
  cong
    (Cook.andBool
      (Cook.evaluate left assignment))
    (rewriteEvaluationExact rewrite assignment)

rewriteEvaluationExact
    (underDisjunctionLeft right rewrite)
    assignment =
  cong
    (λ bit →
      Cook.orBool bit
        (Cook.evaluate right assignment))
    (rewriteEvaluationExact rewrite assignment)

rewriteEvaluationExact
    (underDisjunctionRight left rewrite)
    assignment =
  cong
    (Cook.orBool
      (Cook.evaluate left assignment))
    (rewriteEvaluationExact rewrite assignment)

------------------------------------------------------------------------
-- Evaluation equality -> exact satisfiability equivalence.
------------------------------------------------------------------------

rewriteSatisfiabilityEquivalent :
  ∀ {before after} →
  StructuralRewrite before after →
  Strict.CookSatisfiabilityEquivalent before after
rewriteSatisfiabilityEquivalent rewrite =
  forward , backward
  where
    forward :
      Cook.Satisfiable _ →
      Cook.Satisfiable _
    forward witness =
      Cook.satisfyingAssignment
        (Cook.Satisfiable.assignment witness)
        (trans
          (sym
            (rewriteEvaluationExact
              rewrite
              (Cook.Satisfiable.assignment witness)))
          (Cook.Satisfiable.evaluatesTrue witness))

    backward :
      Cook.Satisfiable _ →
      Cook.Satisfiable _
    backward witness =
      Cook.satisfyingAssignment
        (Cook.Satisfiable.assignment witness)
        (trans
          (rewriteEvaluationExact
            rewrite
            (Cook.Satisfiable.assignment witness))
          (Cook.Satisfiable.evaluatesTrue witness))

------------------------------------------------------------------------
-- Strict node-count descent.
------------------------------------------------------------------------

oneLessTwo : suc zero < suc (suc zero)
oneLessTwo =
  s≤s (s≤s z≤n)

oneLessThree : suc zero < suc (suc (suc zero))
oneLessThree =
  s≤s (s≤s z≤n)

twoSuccessorsAbove :
  (n : Nat) →
  n < suc (suc n)
twoSuccessorsAbove n =
  NatP.<-trans
    (NatP.n<1+n n)
    (NatP.n<1+n (suc n))

formulaCountPositive :
  (formula : Cook.BooleanFormula) →
  suc zero ≤ Size.formulaNodeCount formula
formulaCountPositive (Cook.variable index) =
  s≤s z≤n
formulaCountPositive (Cook.constant value) =
  s≤s z≤n
formulaCountPositive (Cook.negate formula) =
  s≤s z≤n
formulaCountPositive (Cook.conjunction left right) =
  s≤s z≤n
formulaCountPositive (Cook.disjunction left right) =
  s≤s z≤n

constantBelowBinaryWith :
  (formula : Cook.BooleanFormula) →
  suc zero
  <
  suc
    (suc zero
      + Size.formulaNodeCount formula)
constantBelowBinaryWith formula =
  s≤s
    (NatP.≤-trans
      (s≤s z≤n)
      (NatP.m≤m+n
        (suc zero)
        (Size.formulaNodeCount formula)))

constantBelowBinaryRightWith :
  (formula : Cook.BooleanFormula) →
  suc zero
  <
  suc
    (Size.formulaNodeCount formula
      + suc zero)
constantBelowBinaryRightWith formula =
  s≤s
    (NatP.≤-trans
      (formulaCountPositive formula)
      (NatP.m≤m+n
        (Size.formulaNodeCount formula)
        (suc zero)))

liftNegateStrict :
  ∀ {before after : Nat} →
  after < before →
  suc after < suc before
liftNegateStrict strict =
  s≤s strict

liftBinaryLeftStrict :
  ∀ {before after right : Nat} →
  after < before →
  suc (after + right)
  <
  suc (before + right)
liftBinaryLeftStrict {before} {after} {right} strict =
  s≤s
    (NatP.+-mono-≤
      strict
      NatP.≤-refl)

liftBinaryRightStrict :
  ∀ {before after left : Nat} →
  after < before →
  suc (left + after)
  <
  suc (left + before)
liftBinaryRightStrict {before} {after} {left} strict =
  s≤s
    (NatP.+-mono-≤
      NatP.≤-refl
      strict)

rewriteStrictlyDecreases :
  ∀ {before after} →
  StructuralRewrite before after →
  Size.formulaNodeCount after
  <
  Size.formulaNodeCount before

rewriteStrictlyDecreases negateTrue =
  oneLessTwo
rewriteStrictlyDecreases negateFalse =
  oneLessTwo

rewriteStrictlyDecreases (doubleNegation formula) =
  twoSuccessorsAbove
    (Size.formulaNodeCount formula)

rewriteStrictlyDecreases (andTrueLeft formula) =
  twoSuccessorsAbove
    (Size.formulaNodeCount formula)

rewriteStrictlyDecreases (andTrueRight formula) =
  twoSuccessorsAbove
    (Size.formulaNodeCount formula)

rewriteStrictlyDecreases (andFalseLeft formula) =
  constantBelowBinaryWith formula

rewriteStrictlyDecreases (andFalseRight formula) =
  constantBelowBinaryRightWith formula

rewriteStrictlyDecreases (orFalseLeft formula) =
  twoSuccessorsAbove
    (Size.formulaNodeCount formula)

rewriteStrictlyDecreases (orFalseRight formula) =
  twoSuccessorsAbove
    (Size.formulaNodeCount formula)

rewriteStrictlyDecreases (orTrueLeft formula) =
  constantBelowBinaryWith formula

rewriteStrictlyDecreases (orTrueRight formula) =
  constantBelowBinaryRightWith formula

rewriteStrictlyDecreases (underNegate rewrite) =
  liftNegateStrict
    (rewriteStrictlyDecreases rewrite)

rewriteStrictlyDecreases
    (underConjunctionLeft right rewrite) =
  liftBinaryLeftStrict
    (rewriteStrictlyDecreases rewrite)

rewriteStrictlyDecreases
    (underConjunctionRight left rewrite) =
  liftBinaryRightStrict
    (rewriteStrictlyDecreases rewrite)

rewriteStrictlyDecreases
    (underDisjunctionLeft right rewrite) =
  liftBinaryLeftStrict
    (rewriteStrictlyDecreases rewrite)

rewriteStrictlyDecreases
    (underDisjunctionRight left rewrite) =
  liftBinaryRightStrict
    (rewriteStrictlyDecreases rewrite)

------------------------------------------------------------------------
-- Executable chain language: only constants can halt.
------------------------------------------------------------------------

data RewriteProgram :
    Cook.BooleanFormula →
    Set₁ where

  halt :
    (value : Bool) →
    RewriteProgram (Cook.constant value)

  step :
    ∀ {before after} →
    StructuralRewrite before after →
    RewriteProgram after →
    RewriteProgram before

------------------------------------------------------------------------
-- Compile the restricted program to the canonical closed-chain owner.
------------------------------------------------------------------------

compileRewriteProgram :
  ∀ {formula} →
  RewriteProgram formula →
  Closed.StructuralRepresentativeChain formula
compileRewriteProgram (halt value) =
  Closed.terminal value

compileRewriteProgram (step rewrite rest) =
  Closed.descend
    (rewriteSatisfiabilityEquivalent rewrite)
    (rewriteStrictlyDecreases rewrite)
    (compileRewriteProgram rest)

rewriteProgramTruth :
  ∀ {formula} →
  RewriteProgram formula →
  Bool
rewriteProgramTruth program =
  Closed.chainTruth
    (compileRewriteProgram program)

------------------------------------------------------------------------
-- Small regressions demonstrating contextual execution.
------------------------------------------------------------------------

doubleNegatedTrueProgram :
  RewriteProgram
    (Cook.negate
      (Cook.negate
        (Cook.constant true)))
doubleNegatedTrueProgram =
  step
    (doubleNegation (Cook.constant true))
    (halt true)

nestedConjunctionProgram :
  RewriteProgram
    (Cook.conjunction
      (Cook.negate
        (Cook.negate
          (Cook.constant true)))
      (Cook.constant true))
nestedConjunctionProgram =
  step
    (underConjunctionLeft
      (Cook.constant true)
      (doubleNegation
        (Cook.constant true)))
    (step
      (andTrueLeft
        (Cook.constant true))
      (halt true))

nestedConjunctionCompiles :
  Closed.chainTruth
    (compileRewriteProgram nestedConjunctionProgram)
  ≡
  true
nestedConjunctionCompiles =
  refl

------------------------------------------------------------------------
-- ANSWER-BLINDNESS BOUNDARY
--
-- There is no SAT-decider parameter, no Boolean decision oracle, no arbitrary
-- equisatisfiability field, and no finished StructuralRepresentativeChain
-- input to RewriteProgram.
--
-- The only way to advance is one of the constructors above; the compiler
-- derives semantic equivalence and strict descent from the evaluator.
--
-- What remains open is expressivity:
--
--   prove the special Q1 representatives normalize to constants under this
--   language, or identify and add the next independently sound structural
--   rewrite primitive required by the first irreducible representative.
------------------------------------------------------------------------
