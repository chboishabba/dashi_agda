module DASHI.Mathematics.Complexity.PolynomialReductionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Stephen A. Cook,
-- "The complexity of theorem-proving procedures",
-- Proceedings of STOC 1971, 151--158.
-- DOI: 10.1145/800157.805047.
--
-- Richard M. Karp,
-- "Reducibility Among Combinatorial Problems" (1972).
-- No DOI is asserted here.
--
-- DASHI CONTRIBUTION
--
-- Add a reusable exact language/decider/verifier/reduction core.  Polynomial
-- many-one reductions compose, deterministic decision procedures pull back
-- along reductions, and an NP-complete language in P collapses NP into P once
-- the supplied cost model proves closure of polynomial-time decision under
-- polynomial-time precomposition.
--
-- Cook--Levin, concrete machine simulation, clock polynomials and circuit lower
-- bounds remain separate obligations.  A field named polynomial-time is never
-- inferred merely from extensional computability.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

record Iff (left right : Set) : Set where
  constructor iff
  field
    forward : left → right
    backward : right → left

open Iff public

iffReflexive : ∀ proposition → Iff proposition proposition
iffReflexive proposition = iff (λ proof → proof) (λ proof → proof)

iffTransitive : ∀ {left middle right} →
  Iff left middle → Iff middle right → Iff left right
iffTransitive first second =
  iff
    (λ proof → forward second (forward first proof))
    (λ proof → backward first (backward second proof))

record Language (Word : Set) : Set₁ where
  field
    accepts : Word → Set

open Language public

record PolynomialCostModel (Word : Set) : Set₁ where
  field
    polynomialTimeMap : (Word → Word) → Set
    polynomialTimeDecider : (Word → Bool) → Set
    polynomialTimeVerifier : ∀ {Certificate : Set} →
      (Word → Certificate → Bool) → Set
    polynomialCertificateBound : ∀ {Certificate : Set} →
      (Word → Certificate → Set) → Set
    deciderClosedUnderPrecomposition :
      ∀ (map : Word → Word) (decider : Word → Bool) →
      polynomialTimeMap map →
      polynomialTimeDecider decider →
      polynomialTimeDecider (λ word → decider (map word))

open PolynomialCostModel public

record InP {Word : Set}
    (cost : PolynomialCostModel Word)
    (language : Language Word) : Set₁ where
  field
    decide : Word → Bool
    sound : ∀ word → decide word ≡ true → accepts language word
    complete : ∀ word → accepts language word → decide word ≡ true
    polynomialDecision : polynomialTimeDecider cost decide

open InP public

record InNP {Word : Set}
    (cost : PolynomialCostModel Word)
    (language : Language Word) : Set₁ where
  field
    Certificate : Set
    verifies : Word → Certificate → Bool
    certificateAdmissible : Word → Certificate → Set
    sound : ∀ word certificate →
      certificateAdmissible word certificate →
      verifies word certificate ≡ true →
      accepts language word
    complete : ∀ word → accepts language word →
      Certificate × Set
    polynomialVerification : polynomialTimeVerifier cost verifies
    polynomialCertificateSize :
      polynomialCertificateBound cost certificateAdmissible

open InNP public

record PolynomialManyOneReduction
    {Word : Set}
    (cost : PolynomialCostModel Word)
    (source target : Language Word) : Set₁ where
  field
    reduce : Word → Word
    preservesLanguage : ∀ word →
      Iff (accepts source word) (accepts target (reduce word))
    polynomialReduction : polynomialTimeMap cost reduce

open PolynomialManyOneReduction public

identityReduction :
  ∀ {Word} (cost : PolynomialCostModel Word) language →
  PolynomialManyOneReduction cost language language
identityReduction cost language = record
  { reduce = λ word → word
  ; preservesLanguage = λ word → iffReflexive (accepts language word)
  ; polynomialReduction = polynomialTimeMap cost (λ word → word)
  }

record PolynomialMapComposition
    {Word : Set} (cost : PolynomialCostModel Word) : Set₁ where
  field
    composePolynomialMaps : ∀ first second →
      polynomialTimeMap cost first →
      polynomialTimeMap cost second →
      polynomialTimeMap cost (λ word → second (first word))

open PolynomialMapComposition public

composeReduction :
  ∀ {Word} {cost : PolynomialCostModel Word}
    (composition : PolynomialMapComposition cost)
    {first middle last} →
  PolynomialManyOneReduction cost first middle →
  PolynomialManyOneReduction cost middle last →
  PolynomialManyOneReduction cost first last
composeReduction composition firstReduction secondReduction = record
  { reduce = λ word →
      reduce secondReduction (reduce firstReduction word)
  ; preservesLanguage = λ word →
      iffTransitive
        (preservesLanguage firstReduction word)
        (preservesLanguage secondReduction (reduce firstReduction word))
  ; polynomialReduction =
      composePolynomialMaps composition
        (reduce firstReduction)
        (reduce secondReduction)
        (polynomialReduction firstReduction)
        (polynomialReduction secondReduction)
  }

pullbackPAlongReduction :
  ∀ {Word} {cost : PolynomialCostModel Word}
    {source target} →
  PolynomialManyOneReduction cost source target →
  InP cost target →
  InP cost source
pullbackPAlongReduction reduction targetP = record
  { decide = λ word → decide targetP (reduce reduction word)
  ; sound = λ word accepted →
      backward (preservesLanguage reduction word)
        (sound targetP (reduce reduction word) accepted)
  ; complete = λ word sourceProof →
      complete targetP (reduce reduction word)
        (forward (preservesLanguage reduction word) sourceProof)
  ; polynomialDecision =
      deciderClosedUnderPrecomposition _
        (reduce reduction) (decide targetP)
        (polynomialReduction reduction)
        (polynomialDecision targetP)
  }

record NPComplete
    {Word : Set}
    (cost : PolynomialCostModel Word)
    (target : Language Word) : Setω where
  field
    targetInNP : InNP cost target
    everyNPLanguageReduces : ∀ language →
      InNP cost language →
      PolynomialManyOneReduction cost language target

open NPComplete public

record PIncludedInNP
    {Word : Set} (cost : PolynomialCostModel Word) : Setω where
  field
    promotePToNP : ∀ language → InP cost language → InNP cost language

open PIncludedInNP public

record PEqualsNP
    {Word : Set} (cost : PolynomialCostModel Word) : Setω where
  field
    pToNP : ∀ language → InP cost language → InNP cost language
    npToP : ∀ language → InNP cost language → InP cost language

open PEqualsNP public

npCompleteInPImpliesPEqualsNP :
  ∀ {Word} {cost : PolynomialCostModel Word}
    (pSubsetNP : PIncludedInNP cost)
    (target : Language Word) →
  NPComplete cost target →
  InP cost target →
  PEqualsNP cost
npCompleteInPImpliesPEqualsNP pSubsetNP target completeTarget targetP = record
  { pToNP = promotePToNP pSubsetNP
  ; npToP = λ language languageNP →
      pullbackPAlongReduction
        (everyNPLanguageReduces completeTarget language languageNP)
        targetP
  }
