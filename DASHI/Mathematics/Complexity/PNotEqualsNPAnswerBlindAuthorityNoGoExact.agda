module DASHI.Mathematics.Complexity.PNotEqualsNPAnswerBlindAuthorityNoGoExact where

------------------------------------------------------------------------
-- ANSWER-BLIND AUTHORITY NO-GO
--
-- Companion to:
--   PNotEqualsNPSemanticAuthorityConstructionNoGoExact
--
-- The omniscient constructor theorem showed one extreme:
--
--   if an authority constructor may first evaluate f(x), then it can emit the
--   one-node formula constant(f x).
--
-- This owner pays the opposite extreme.
--
-- Suppose the authority emitted for a fixed input x is independent of WHICH
-- Boolean computation is being certified.  Then the same authority cannot be
-- exact for two computations that disagree at x.
--
-- Therefore the useful P11 constructor must occupy the middle ground:
--
--   * it MUST depend on the finite program description / intensional structure;
--   * it MUST NOT obtain its short authority merely by first evaluating the
--     target decision and printing that result.
--
-- This is a small theorem, but it makes the non-circularity requirement typed
-- rather than editorial.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

------------------------------------------------------------------------
-- Exact semantic authority for one Boolean computation at one input.
------------------------------------------------------------------------

record ExactSemanticAuthority
    {Input : Set}
    (decision : Input → Bool)
    (input : Input)
    (authority : Cook.BooleanFormula) : Set₁ where
  constructor exact-semantic-authority
  field
    complete :
      decision input ≡ true →
      Cook.Satisfiable authority

    sound :
      Cook.Satisfiable authority →
      decision input ≡ true

open ExactSemanticAuthority public

------------------------------------------------------------------------
-- Same authority cannot exactly certify two disagreeing decisions.
------------------------------------------------------------------------

sameAuthorityCannotCertifyOppositeAnswers :
  ∀ {Input : Set}
    {leftDecision rightDecision : Input → Bool}
    {input : Input}
    {authority : Cook.BooleanFormula} →
  leftDecision input ≡ true →
  rightDecision input ≡ false →
  ExactSemanticAuthority
    leftDecision input authority →
  ExactSemanticAuthority
    rightDecision input authority →
  ⊥
sameAuthorityCannotCertifyOppositeAnswers
    leftTrue rightFalse
    leftAuthority rightAuthority =
  falseNotTrue
    (trans
      (sym rightFalse)
      (sound rightAuthority
        (complete leftAuthority leftTrue)))

------------------------------------------------------------------------
-- Answer-blind constructor.
--
-- It may inspect the INPUT, but not a program/decision description.
------------------------------------------------------------------------

AnswerBlindAuthorityConstructor :
  Set →
  Set
AnswerBlindAuthorityConstructor Input =
  Input → Cook.BooleanFormula

answerBlindConstructorCannotBeExactForAllDecisions :
  ∀ {Input : Set}
    (constructor : AnswerBlindAuthorityConstructor Input)
    (input : Input)
    (leftDecision rightDecision : Input → Bool) →
  leftDecision input ≡ true →
  rightDecision input ≡ false →
  ExactSemanticAuthority
    leftDecision
    input
    (constructor input) →
  ExactSemanticAuthority
    rightDecision
    input
    (constructor input) →
  ⊥
answerBlindConstructorCannotBeExactForAllDecisions
    constructor input
    leftDecision rightDecision
    leftTrue rightFalse
    leftAuthority rightAuthority =
  sameAuthorityCannotCertifyOppositeAnswers
    leftTrue
    rightFalse
    leftAuthority
    rightAuthority

------------------------------------------------------------------------
-- Concrete disagreement exists at every inhabited input type.
------------------------------------------------------------------------

alwaysTrueDecision :
  ∀ {Input : Set} →
  Input →
  Bool
alwaysTrueDecision input =
  true

alwaysFalseDecision :
  ∀ {Input : Set} →
  Input →
  Bool
alwaysFalseDecision input =
  false

answerBlindConstructorHasConcreteOppositePair :
  ∀ {Input : Set}
    (constructor : AnswerBlindAuthorityConstructor Input)
    (input : Input) →
  ExactSemanticAuthority
    alwaysTrueDecision
    input
    (constructor input) →
  ExactSemanticAuthority
    alwaysFalseDecision
    input
    (constructor input) →
  ⊥
answerBlindConstructorHasConcreteOppositePair
    constructor input =
  answerBlindConstructorCannotBeExactForAllDecisions
    constructor
    input
    alwaysTrueDecision
    alwaysFalseDecision
    refl
    refl

------------------------------------------------------------------------
-- Research consequence.
--
-- The missing P11 authority constructor cannot be:
--
--   * answer-omniscient: that makes one-node authorities trivial; or
--   * program-blind: then it cannot distinguish opposite computations.
--
-- It must consume a finite intensional description of D and derive its short
-- authority from structure of that description/self-input under a separately
-- bounded construction process.
------------------------------------------------------------------------
