module DASHI.Cognition.PNF.ContextualFractranTopDownObservationExact where

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.TopDownObservationCalculusExact as TopDown
import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Cognition.PNF.ContextualFractranFibreRestrictionExact as Fibre
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Foundations.SSPTritCarrier as Trit

------------------------------------------------------------------------
-- The repository-wide top-down observation calculus applies literally to a
-- requested prime observation of a complete contextual signed valuation.
-- Consumer adequacy, reconstruction, operation descent and representation
-- economy remain separate obligations.
------------------------------------------------------------------------

record ContextualPrimeConsumerProblem : Set₁ where
  constructor contextualPrimeConsumerProblem
  field
    Outcome : Set
    requestedPrime : Signed.SSPPrime
    consume : Context.ContextualValuation → Outcome

open ContextualPrimeConsumerProblem public

toObservationProblem :
  ContextualPrimeConsumerProblem → TopDown.ConsumerObservationProblem
toObservationProblem problem =
  TopDown.consumerObservationProblem
    Context.ContextualValuation
    Trit.SSPTrit
    (Outcome problem)
    (Fibre.projectRequestedPrime (requestedPrime problem))
    (consume problem)

ContextualConsumerAdequate : ContextualPrimeConsumerProblem → Set
ContextualConsumerAdequate problem =
  TopDown.Adequate (toObservationProblem problem)

ContextualReconstructive : ContextualPrimeConsumerProblem → Set
ContextualReconstructive problem =
  TopDown.Reconstructive (toObservationProblem problem)

reconstructionIsStrongerThanDeclaredConsumerNeed :
  (problem : ContextualPrimeConsumerProblem) →
  ContextualReconstructive problem →
  ContextualConsumerAdequate problem
reconstructionIsStrongerThanDeclaredConsumerNeed problem =
  TopDown.reconstructionImpliesConsumerAdequacy (toObservationProblem problem)

record ContextualTopDownBoundary : Set where
  constructor contextualTopDownBoundary
  field
    onePrimeObservationMustReconstructWholeValuation : Bool
    consumerAdequacyMayHoldWithoutReconstruction : Bool
    operationDescentRequiresOwnProof : Bool
    representationEconomyIsSeparateObjective : Bool

canonicalContextualTopDownBoundary : ContextualTopDownBoundary
canonicalContextualTopDownBoundary =
  contextualTopDownBoundary false true true true
