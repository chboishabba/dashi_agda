module DASHI.Cognition.PNF.WaveAccessBraidOrderExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.BraidLearningTransport as Braid

------------------------------------------------------------------------
-- Fast access-control operations need not commute.  This supplies a concrete
-- producer shape for the existing braid-order residual while keeping the
-- logical implication one-way: the existing abstract braid residual is not
-- thereby identified with a neural-wave cause.
------------------------------------------------------------------------

record AccessRegister : Set where
  constructor accessRegister
  field
    threatAccessible : Bool
    safetyAccessible : Bool

open AccessRegister public

baseline : AccessRegister
baseline = accessRegister false false

threatPrime : AccessRegister → AccessRegister
threatPrime (accessRegister threat safety) =
  accessRegister true safety

coupledSafetyReadout : AccessRegister → AccessRegister
coupledSafetyReadout (accessRegister threat safety) =
  accessRegister threat threat

primeThenReadout : AccessRegister
primeThenReadout = coupledSafetyReadout (threatPrime baseline)

readoutThenPrime : AccessRegister
readoutThenPrime = threatPrime (coupledSafetyReadout baseline)

primeThenReadoutIsBothAccessible :
  primeThenReadout ≡ accessRegister true true
primeThenReadoutIsBothAccessible = refl

readoutThenPrimeLeavesSafetyClosed :
  readoutThenPrime ≡ accessRegister true false
readoutThenPrimeLeavesSafetyClosed = refl

ordersDiffer : primeThenReadout ≡ readoutThenPrime → ⊥
ordersDiffer ()

existingBraidIsResiduallyDifferent :
  Braid.comparison Braid.canonicalNonCommutingBraid
  ≡ Braid.residuallyDifferent
existingBraidIsResiduallyDifferent = refl

record PhysicalAccessBraidBridge : Set where
  constructor physicalAccessBraidBridge
  field
    concreteFastOrderNoncommutes :
      primeThenReadout ≡ readoutThenPrime → ⊥
    existingAbstractBraid : Braid.BraidOrderReceipt
    existingAbstractBraidIsResidual :
      Braid.comparison existingAbstractBraid ≡ Braid.residuallyDifferent
    abstractBraidProvesNeuralWaveCause : Bool

canonicalPhysicalAccessBraidBridge : PhysicalAccessBraidBridge
canonicalPhysicalAccessBraidBridge =
  physicalAccessBraidBridge
    ordersDiffer
    Braid.canonicalNonCommutingBraid
    refl
    false
