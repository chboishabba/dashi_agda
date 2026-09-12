module DASHI.ComputerScience.UniversalComputabilityExternalResultExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- UNIVERSAL COMPUTATION RESULT CONTRACTS
--
-- These are model-relative.  A theorem over AFP Turing machines, Coq Busy
-- Beaver machines, or another universal model must retain that model identity;
-- it does not automatically become a theorem about DASHI's tiny register ISA.
------------------------------------------------------------------------

record UniversalComputationSource : Set₁ where
  field
    Program : Set
    Input : Set
    Halts : Program → Input → Set
    zeroInput : Input
    size : Program → Nat

open UniversalComputationSource public

record ExactHaltingDecider
    (S : UniversalComputationSource) : Set where
  constructor exactHaltingDecider
  field
    decide : Program S → Input S → Bool
    positiveSound :
      (p : Program S) → (i : Input S) →
      decide p i ≡ true → Halts S p i
    negativeSound :
      (p : Program S) → (i : Input S) →
      decide p i ≡ false → Halts S p i → ⊥

open ExactHaltingDecider public

record ExactZeroInputHaltingDecider
    (S : UniversalComputationSource) : Set where
  constructor exactZeroInputHaltingDecider
  field
    decideZero : Program S → Bool
    zeroPositiveSound :
      (p : Program S) →
      decideZero p ≡ true → Halts S p (zeroInput S)
    zeroNegativeSound :
      (p : Program S) →
      decideZero p ≡ false → Halts S p (zeroInput S) → ⊥

open ExactZeroInputHaltingDecider public

record UniversalHaltingUndecidabilityResult
    (S : UniversalComputationSource) : Set₁ where
  constructor universalHaltingUndecidabilityResult
  field
    noExactTotalHaltingDecider : ExactHaltingDecider S → ⊥

open UniversalHaltingUndecidabilityResult public

------------------------------------------------------------------------
-- BUSY BEAVER UPPER-BOUND PRINCIPLE
------------------------------------------------------------------------

record BusyBeaverUpperBoundPrinciple
    (S : UniversalComputationSource) : Set₁ where
  constructor busyBeaverUpperBoundPrinciple
  field
    busyBeaverTime : Nat → Nat
    upperBoundToZeroInputDecider :
      (upper : Nat → Nat) →
      ((n : Nat) → busyBeaverTime n ≤ upper n) →
      ExactZeroInputHaltingDecider S

open BusyBeaverUpperBoundPrinciple public

------------------------------------------------------------------------
-- An external machine-checked source may provide both coordinates on the SAME
-- machine model.  This is the direct target for the 2026 Isabelle/AFP result.
------------------------------------------------------------------------

record UniversalComputabilityPayment : Set₁ where
  constructor universalComputabilityPayment
  field
    source : UniversalComputationSource
    haltingUndecidability : UniversalHaltingUndecidabilityResult source
    busyBeaverUpperBound : BusyBeaverUpperBoundPrinciple source
    modelIdentity : String
    sourceRevision : String

open UniversalComputabilityPayment public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data BoundedNotHaltedYetIsNonHaltingProof : Set where
data TernaryRuntimeObserverIsTotalHaltingDecider : Set where
data FiniteBusyBeaverEnvelopeIsUniversalBusyBeaver : Set where
data DifferentMachineModelsShareUndecidabilityProofByDefinition : Set where

boundedObservationDoesNotProveDivergence :
  BoundedNotHaltedYetIsNonHaltingProof → ⊥
boundedObservationDoesNotProveDivergence ()

ternaryObserverDoesNotBecomeTotalDecider :
  TernaryRuntimeObserverIsTotalHaltingDecider → ⊥
ternaryObserverDoesNotBecomeTotalDecider ()

finiteEnvelopeDoesNotBecomeUniversalBusyBeaver :
  FiniteBusyBeaverEnvelopeIsUniversalBusyBeaver → ⊥
finiteEnvelopeDoesNotBecomeUniversalBusyBeaver ()

machineModelsNeedAdapter :
  DifferentMachineModelsShareUndecidabilityProofByDefinition → ⊥
machineModelsNeedAdapter ()

record UniversalComputabilityBoundary : Set where
  constructor universalComputabilityBoundary
  field
    modelRelativeHaltingResultContractOwned : Bool
    modelRelativeBusyBeaverUpperBoundContractOwned : Bool
    boundedTernaryObserverAcceptedAsTotalDecider : Bool
    finiteEnvelopeAcceptedAsUniversalBusyBeaver : Bool
    isabelleAFPPaymentInhabitantOwned : Bool

canonicalUniversalComputabilityBoundary : UniversalComputabilityBoundary
canonicalUniversalComputabilityBoundary =
  universalComputabilityBoundary true true false false false
