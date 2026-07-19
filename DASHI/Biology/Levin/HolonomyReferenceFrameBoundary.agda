module DASHI.Biology.Levin.HolonomyReferenceFrameBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record InternalTransportPath : Set where
  field
    closedPath : Bool
    transportedWithoutLocalRotation : Bool
    returnedWithPhaseDefect : Bool

record ReferenceFrameChangeWitness : Set where
  field
    path : InternalTransportPath
    observableActionChanged : Bool
    orderOfOperationsMatters : Bool

record HolonomyBoundary : Set where
  field
    geometricPhaseRequiresClosedTransportWitness : Bool
    referenceFrameChangeRequiresOperationalWitness : Bool
    noncommutativityDoesNotAutomaticallyImplyQuantumEntanglement : Bool
    biologicalHolonomyDoesNotAutomaticallyImplyUniversalComputation : Bool
    interpretation : String

canonicalHolonomyBoundary : HolonomyBoundary
canonicalHolonomyBoundary = record
  { geometricPhaseRequiresClosedTransportWitness = true
  ; referenceFrameChangeRequiresOperationalWitness = true
  ; noncommutativityDoesNotAutomaticallyImplyQuantumEntanglement = true
  ; biologicalHolonomyDoesNotAutomaticallyImplyUniversalComputation = true
  ; interpretation = "Internal transport may alter effective biological reference frames, but holonomy, contextuality and computational universality require separate witnesses"
  }
