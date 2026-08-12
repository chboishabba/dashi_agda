module DASHI.Core.QueryFactorisationSufficiency where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- QUERY FACTORISATION SUFFICIENCY
--
-- Classical statistical sufficiency motivates the separation between a
-- reduction that preserves every authorised present query and a claim that the
-- represented model exhausts the underlying world.  DASHI uses the more
-- general factorisation surface below; no probabilistic model is assumed.
--
-- Reference / motivation:
--   R. A. Fisher's sufficient-statistic tradition; this file intentionally
--   cites the concept rather than attributing the generic factorisation theorem
--   below to a particular statistics paper.
--
-- Core law:
--
--   q = qbar o pi
--
-- means q can be answered entirely from the quotient pi.  It says nothing
-- about world/model completeness and nothing about future dynamic safety.
------------------------------------------------------------------------

record InquiryQuestionFamily (State Query : Set) : Set₁ where
  constructor inquiryQuestionFamily
  field
    Answer : Query → Set
    ask : (query : Query) → State → Answer query

open InquiryQuestionFamily public

record FactorsThrough
    {State Surface Query : Set}
    (questions : InquiryQuestionFamily State Query)
    (project : State → Surface)
    (query : Query) : Set₁ where
  constructor factorsThrough
  field
    quotientAnswer : Surface → Answer questions query
    factorisation :
      (state : State) →
      ask questions query state ≡ quotientAnswer (project state)

open FactorsThrough public

record StaticSufficient
    {State Surface Query : Set}
    (questions : InquiryQuestionFamily State Query)
    (project : State → Surface) : Set₁ where
  constructor staticSufficient
  field
    factorFor :
      (query : Query) →
      FactorsThrough questions project query

open StaticSufficient public

------------------------------------------------------------------------
-- Static sufficiency and world coverage are differently typed obligations.
-- There is deliberately no constructor from StaticSufficient to the separate
-- ConsumerIndexedRelevanceMeasure.WorldCoverageWitness surface.
------------------------------------------------------------------------

data StaticSufficiencyWorldCoveragePermission : Set where

staticSufficiencyCannotManufactureWorldCoverage :
  StaticSufficiencyWorldCoveragePermission → ⊥
staticSufficiencyCannotManufactureWorldCoverage ()

------------------------------------------------------------------------
-- Finite witness: a quotient can be exactly sufficient for the only authorised
-- present query while still carrying a hidden state distinction.
------------------------------------------------------------------------

data DemoState : Set where
  visibleLeft visibleRight : DemoState

data DemoSurface : Set where
  sameSurface : DemoSurface

data DemoQuery : Set where
  whoQuestion : DemoQuery

data DemoAnswer : Set where
  johnAnswer : DemoAnswer

demoQuestions : InquiryQuestionFamily DemoState DemoQuery
demoQuestions = inquiryQuestionFamily (λ query → DemoAnswer) askDemo
  where
    askDemo : (query : DemoQuery) → DemoState → DemoAnswer
    askDemo whoQuestion visibleLeft = johnAnswer
    askDemo whoQuestion visibleRight = johnAnswer

demoProject : DemoState → DemoSurface
demoProject visibleLeft = sameSurface
demoProject visibleRight = sameSurface

demoWhoFactors : FactorsThrough demoQuestions demoProject whoQuestion
demoWhoFactors = factorsThrough quotientAnswer proof
  where
    quotientAnswer : DemoSurface → DemoAnswer
    quotientAnswer sameSurface = johnAnswer

    proof :
      (state : DemoState) →
      ask demoQuestions whoQuestion state ≡ quotientAnswer (demoProject state)
    proof visibleLeft = refl
    proof visibleRight = refl

demoProjectionIsStaticallySufficient :
  StaticSufficient demoQuestions demoProject
demoProjectionIsStaticallySufficient = staticSufficient factor
  where
    factor : (query : DemoQuery) → FactorsThrough demoQuestions demoProject query
    factor whoQuestion = demoWhoFactors
