module DASHI.Core.ConsumerRelativeRepresentationParityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.QueryFactorisationSufficiency as Factor
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as Admission

------------------------------------------------------------------------
-- CONSUMER-RELATIVE REPRESENTATION PARITY
--
-- Two representations are consumer-parity equivalents only relative to the
-- declared inquiry family.  No claim of world-complete semantic identity is
-- made.  This owner reuses the existing factorisation and admissible/adequate
-- selection contracts instead of defining another adequacy calculus.
------------------------------------------------------------------------

record ConsumerParity
    {State Left Right Query : Set}
    (questions : Factor.InquiryQuestionFamily State Query)
    (left : State → Left)
    (right : State → Right) : Set₁ where
  constructor consumerParity
  field
    leftSufficient : Factor.StaticSufficient questions left
    rightSufficient : Factor.StaticSufficient questions right

open ConsumerParity public

leftFactors :
  ∀ {State Left Right Query}
    {questions : Factor.InquiryQuestionFamily State Query}
    {left : State → Left}
    {right : State → Right} →
  ConsumerParity questions left right →
  (query : Query) →
  Factor.FactorsThrough questions left query
leftFactors parity = Factor.factorFor (leftSufficient parity)

rightFactors :
  ∀ {State Left Right Query}
    {questions : Factor.InquiryQuestionFamily State Query}
    {left : State → Left}
    {right : State → Right} →
  ConsumerParity questions left right →
  (query : Query) →
  Factor.FactorsThrough questions right query
rightFactors parity = Factor.factorFor (rightSufficient parity)

------------------------------------------------------------------------
-- Canonical admissibility/consumer-adequacy instantiation.
--
-- ConsumerAdequate is definitionally the existing StaticSufficient obligation
-- for the selected representation.  Admissibility remains application-owned.
-- Complexity/description length is considered only after both are inhabited.
------------------------------------------------------------------------

representationProblem :
  ∀ {State Surface Query Model : Set} →
  (questions : Factor.InquiryQuestionFamily State Query) →
  (representation : Model → State → Surface) →
  (admissible : Model → Set) →
  (descriptionLength : Model → Nat) →
  (refines : Model → Model → Set) →
  (modelReference : Model → String) →
  (codingConventionReference consumerReference : String) →
  Admission.ConsumerMDLProblem
representationProblem {Model = Model}
    questions representation admissible descriptionLength refines modelReference
    codingConventionReference consumerReference =
  Admission.consumerMDLProblem
    Model
    admissible
    (λ model → Factor.StaticSufficient questions (representation model))
    descriptionLength
    refines
    modelReference
    codingConventionReference
    consumerReference

staticSufficiencyPaysConsumerAdequacy :
  ∀ {State Surface Query Model : Set}
    {questions : Factor.InquiryQuestionFamily State Query}
    {representation : Model → State → Surface}
    {admissible : Model → Set}
    {descriptionLength : Model → Nat}
    {refines : Model → Model → Set}
    {modelReference : Model → String}
    {codingConventionReference consumerReference : String}
    {model : Model} →
  Factor.StaticSufficient questions (representation model) →
  Admission.ConsumerAdequate
    (representationProblem questions representation admissible descriptionLength
      refines modelReference codingConventionReference consumerReference)
    model
staticSufficiencyPaysConsumerAdequacy sufficient = sufficient

admissibleAndStaticSufficientAreEligible :
  ∀ {State Surface Query Model : Set}
    {questions : Factor.InquiryQuestionFamily State Query}
    {representation : Model → State → Surface}
    {admissible : Model → Set}
    {descriptionLength : Model → Nat}
    {refines : Model → Model → Set}
    {modelReference : Model → String}
    {codingConventionReference consumerReference : String}
    {model : Model} →
  admissible model →
  Factor.StaticSufficient questions (representation model) →
  Admission.Eligible
    (representationProblem questions representation admissible descriptionLength
      refines modelReference codingConventionReference consumerReference)
    model
admissibleAndStaticSufficientAreEligible admissibleReceipt sufficient =
  admissibleReceipt , staticSufficiencyPaysConsumerAdequacy sufficient

------------------------------------------------------------------------
-- Information-order bridge.
------------------------------------------------------------------------

representationRefinement :
  ∀ {State Coarse Fine : Set} →
  (coarse : State → Coarse) →
  (fine : State → Fine) →
  Set
representationRefinement = Observer.Refines

record ConsumerParityBoundary : Set where
  constructor consumerParityBoundary
  field
    parityIsConsumerIndexed : Bool
    parityRequiresBothStaticSufficiencyReceipts : Bool
    admissibilityRemainsSeparateFromConsumerAdequacy : Bool
    complexityRanksOnlyAfterEligibility : Bool
    parityImpliesWorldCompleteSemanticIdentity : Bool

canonicalConsumerParityBoundary : ConsumerParityBoundary
canonicalConsumerParityBoundary =
  consumerParityBoundary true true true true false
