module DASHI.ComputerScience.BoundedBusyBeaverExecutionEnvelopeExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.TinyRadixNeutralRegisterMachineExact as Machine
import DASHI.ComputerScience.EuclidGCDRegisterMachineExact as Euclid
import DASHI.ComputerScience.ClassicalOrderFindingRegisterMachineExact as Order

------------------------------------------------------------------------
-- BOUNDED BUSY-BEAVER-STYLE EXECUTION ENVELOPE
--
-- This is a finite maximum over an explicitly listed set of already certified
-- terminating executions.  It is useful as the executable finite analogue of
-- a Busy-Beaver-style observer, but it is deliberately NOT the universal Busy
-- Beaver function and proves no non-computability theorem.
------------------------------------------------------------------------

maxNat : Nat → Nat → Nat
maxNat zero m = m
maxNat (suc n) zero = suc n
maxNat (suc n) (suc m) = suc (maxNat n m)

maxList : List Nat → Nat
maxList [] = 0
maxList (n ∷ ns) = maxNat n (maxList ns)

------------------------------------------------------------------------
-- Certified runtime samples from the existing executable machine stack.
------------------------------------------------------------------------

countdown3Runtime : Nat
countdown3Runtime = Machine.cycles (Machine.countdownFinal 3)

countdown3RuntimeExact : countdown3Runtime ≡ 14
countdown3RuntimeExact = Machine.countdownThreeCycles

euclid4818Runtime : Nat
euclid4818Runtime = Machine.cycles Euclid.euclid4818Final

euclid4818RuntimeExact : euclid4818Runtime ≡ 19
euclid4818RuntimeExact = Euclid.euclid4818Cycles

order15Runtime : Nat
order15Runtime = Machine.cycles Order.order15Final

order15RuntimeExact : order15Runtime ≡ 17
order15RuntimeExact = Order.order15Cycles

order21Runtime : Nat
order21Runtime = Machine.cycles Order.order21Final

order21RuntimeExact : order21Runtime ≡ 25
order21RuntimeExact = Order.order21Cycles

runtimeSample : List Nat
runtimeSample =
  countdown3Runtime
  ∷ euclid4818Runtime
  ∷ order15Runtime
  ∷ order21Runtime
  ∷ []

boundedRuntimeEnvelope : Nat
boundedRuntimeEnvelope = maxList runtimeSample

boundedRuntimeEnvelopeIs25 : boundedRuntimeEnvelope ≡ 25
boundedRuntimeEnvelopeIs25 = refl

------------------------------------------------------------------------
-- Exact provenance of the selected finite maximum.
------------------------------------------------------------------------

record BoundedRuntimeEnvelopeReceipt : Set where
  constructor boundedRuntimeEnvelopeReceipt
  field
    candidateCount : Nat
    selectedMaximum : Nat
    selectedMaximumExact : selectedMaximum ≡ 25
    finiteCandidateSet : Bool
    allCandidatesAlreadyHaveHaltingReceipts : Bool
    universalProgramSpaceCovered : Bool
    universalBusyBeaverClaimed : Bool
    nonComputabilityClaimedFromFiniteMaximum : Bool

canonicalBoundedRuntimeEnvelopeReceipt : BoundedRuntimeEnvelopeReceipt
canonicalBoundedRuntimeEnvelopeReceipt =
  boundedRuntimeEnvelopeReceipt
    4
    boundedRuntimeEnvelope
    boundedRuntimeEnvelopeIs25
    true
    true
    false
    false
    false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data FiniteEnvelopeEqualsBusyBeaver : Set where
data FiniteMaximumProvesNonComputability : Set where

finiteEnvelopeDoesNotBecomeUniversalBusyBeaver :
  FiniteEnvelopeEqualsBusyBeaver → ⊥
finiteEnvelopeDoesNotBecomeUniversalBusyBeaver ()

finiteMaximumDoesNotProveNonComputability :
  FiniteMaximumProvesNonComputability → ⊥
finiteMaximumDoesNotProveNonComputability ()
