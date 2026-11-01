module DASHI.Physics.Closure.WitnessSetPolicyShiftInstance where

open import Agda.Builtin.Nat using (Nat)
open import Data.Unit using (⊤; tt)

open import DASHI.Physics.WitnessSetPolicy as WSP

-- Concrete witness-set policy instance for shift closures.
-- Counts and quota are left abstract; this is a wiring point for evidence.
record WitnessSetShift : Set₁ where
  field
    forwardCount : Nat
    backwardCount : Nat
    quotaPreserving : Set

open WitnessSetShift public

policyShift : WSP.WitnessSetPolicy WitnessSetShift
policyShift =
  record
    { minForward = 3
    ; minBackward = 3
    ; forwardCount = WitnessSetShift.forwardCount
    ; backwardCount = WitnessSetShift.backwardCount
    ; quotaPreserving = WitnessSetShift.quotaPreserving
    }
