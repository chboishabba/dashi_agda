module DASHI.Cognition.PNF.ContextualFractranArgumentTransportExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Core.ArgumentObstructionCore as Argument
import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed

------------------------------------------------------------------------
-- Cheap trit/prime inversion is not generic argument inversion. An argument is
-- governed transport with rule, evidence, context, time, meaning, cause and
-- modality. Reciprocal FRACTRAN transport can only reverse its phase component.
------------------------------------------------------------------------

record ArgumentPhaseProjection (core : Argument.ArgumentCore) : Set₁ where
  constructor argumentPhaseProjection
  field
    argument : Argument.ArgumentWitness core
    phaseRoles : Context.OrientedRolePair
    phaseValuation : Context.ContextualValuation
    residualArgument : Argument.ArgumentWitness core

open ArgumentPhaseProjection public

record CandidateArgumentReverse (core : Argument.ArgumentCore) : Set₁ where
  constructor candidateArgumentReverse
  field
    before : ArgumentPhaseProjection core
    reversedPhase : Context.ContextualValuation
    phaseIsNegated :
      (prime : Signed.SSPPrime) →
      reversedPhase prime ≡ Context.negateValuation (phaseValuation before) prime

    -- Sign reversal manufactures none of these governed-transport obligations.
    ReverseRule : Set
    ReverseReceipt : Set
    ReverseContext : Set
    ReverseMeaning : Set
    ReverseCause : Set
    ReverseModality : Set

record ArgumentFractranBoundary : Set where
  constructor argumentFractranBoundary
  field
    polarityInversionIsCheap : Bool
    reciprocalFractionAutomaticallyReversesArgument : Bool
    reverseArgumentNeedsNewGovernedTransportObligations : Bool
    argumentObstructionRefutesConclusion : Bool

canonicalArgumentFractranBoundary : ArgumentFractranBoundary
canonicalArgumentFractranBoundary =
  argumentFractranBoundary true false true false
