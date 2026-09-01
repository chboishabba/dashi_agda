module DASHI.Cognition.PNF.ContextualFractranArgumentTransportExact where

open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Core.ArgumentObstructionCore as Argument
import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context

------------------------------------------------------------------------
-- Cheap trit/prime inversion is not generic argument inversion.  An argument
-- is already a governed transport object with rule, evidence, context, time,
-- meaning, cause and modality.  Reciprocal FRACTRAN transport can therefore be
-- only the orientation component of a candidate reverse argument.
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
      (prime : _) →
      reversedPhase prime ≡ Context.negateValuation (phaseValuation before) prime

    -- The new governed-transport obligations are explicit sockets.  Nothing in
    -- sign reversal manufactures them.
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
