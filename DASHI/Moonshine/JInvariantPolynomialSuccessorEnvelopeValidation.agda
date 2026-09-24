module DASHI.Moonshine.JInvariantPolynomialSuccessorEnvelopeValidation where

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_≤_)

import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Power
import DASHI.Moonshine.JInvariantPolynomialSuccessorEnvelopeExact as P

degreeFourSuccessorEnvelope :
  ∀ n → 1 ≤ n →
  Power.powNat (suc n) 4
    ≤ Power.powNat n 4 + 15 * Power.powNat n 3
degreeFourSuccessorEnvelope = P.degreeFourSuccessorEnvelope

degreeSixSuccessorEnvelope :
  ∀ n → 1 ≤ n →
  Power.powNat (suc n) 6
    ≤ Power.powNat n 6 + 63 * Power.powNat n 5
degreeSixSuccessorEnvelope = P.degreeSixSuccessorEnvelope
