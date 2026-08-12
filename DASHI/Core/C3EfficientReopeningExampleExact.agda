module DASHI.Core.C3EfficientReopeningExampleExact where

------------------------------------------------------------------------
-- CONCRETE EFFICIENT-REOPENING EXAMPLE
--
-- The same three-point C3 carrier used by the orbit quotient is turned into a
-- witness problem whose coarse instance is a single point and whose receipt is
-- the fine C3 coordinate.  Reopening is exact, and all four accounting costs
-- are certified by a constant polynomial bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Core.EfficientRecoverableQuotientExact as ERQ

c3WitnessProblem : ERQ.WitnessProblem
c3WitnessProblem =
  ERQ.witnessProblem C3.C3 C3.C3 _≡_

c3WitnessRecoverableQuotient : ERQ.WitnessRecoverableQuotient c3WitnessProblem
c3WitnessRecoverableQuotient =
  ERQ.witnessRecoverableQuotient
    ⊤
    C3.C3
    (λ _ → tt)
    (λ x → x)
    (λ _ receipt → receipt)
    (λ x → refl)

one : Nat
one = suc zero

constantOne : Nat → Nat
constantOne _ = one

onePolynomial : ERQ.PolynomialBound constantOne
onePolynomial =
  ERQ.polynomialBound one zero (λ n → s≤s z≤n)

c3EfficientRecoverableFamily : ERQ.EfficientRecoverableFamily
c3EfficientRecoverableFamily =
  ERQ.efficientRecoverableFamily
    constantOne
    constantOne
    constantOne
    constantOne
    onePolynomial
    onePolynomial
    onePolynomial
    onePolynomial

c3ReopeningVerifiesExactly : ∀ x →
  ERQ.verifies c3WitnessProblem x
    (ERQ.reopenWitness c3WitnessRecoverableQuotient
      (ERQ.project c3WitnessRecoverableQuotient x)
      (ERQ.receipt c3WitnessRecoverableQuotient x))
c3ReopeningVerifiesExactly x = refl
