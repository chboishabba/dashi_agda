module DASHI.Cognition.PNF.ContextualFractranDirectDeltaAdapterExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Cognition.PNF.ContextualFractranOccurrenceHyperfabricExact as Context
import DASHI.Cognition.PNF.DirectDeltaCompilerArchitectureExact as Direct
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed

------------------------------------------------------------------------
-- The direct compiler already defines execution-vs-authority boundaries,
-- natural child/parent delta transport, consumer observation parity, and the
-- exact outward-delta fixed point.  This adapter does not add a second runtime;
-- it states what a contextual FRACTRAN implementation must expose to that one.
------------------------------------------------------------------------

record ContextualFractranDirectAdapter : Set₁ where
  constructor contextualFractranDirectAdapter
  field
    backwardLaw : Context.BackwardDerivationLaw
    requestedPrime : Signed.SSPPrime

    directObservation : Context.RequestedPrimeObservation
    referenceObservation : Context.RequestedPrimeObservation
    directReferenceParity :
      Direct.DirectReferenceParity Context.RequestedPrimeObservation

    -- The semantic machine may reach a direct-delta fixed point while still
    -- retaining unresolved world fibres.  Fixed point means no outward delta,
    -- not uniqueness of the fine interpretation.
    executionFixedPoint : Direct.DirectDeltaFixedPointReceipt
    retainedResidual : Context.ResidualWorldFibre

open ContextualFractranDirectAdapter public

record BackwardForwardBidiLaw
  (Global Local : Set)
  : Set₁ where
  constructor backwardForwardBidiLaw
  field
    restrict : Global → Local
    publishObservation : Local → Context.RequestedPrimeObservation
    reconstructObservation : Global → Context.RequestedPrimeObservation
    observationCommutes :
      (global : Global) →
      publishObservation (restrict global) ≡ reconstructObservation global

open BackwardForwardBidiLaw public

record DirectContextualBoundary : Set where
  constructor directContextualBoundary
  field
    requiresSecondRelationalRuntime : Bool
    parserTokenRowIsSemanticAuthority : Bool
    directFixedPointMeansUniqueWorld : Bool
    consumerParityCanIgnoreFineExecutionIdentity : Bool
    backwardRestrictionNeedsObservationCommutation : Bool

canonicalDirectContextualBoundary : DirectContextualBoundary
canonicalDirectContextualBoundary =
  directContextualBoundary false false false true true
