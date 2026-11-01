module DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterRegression where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector

------------------------------------------------------------------------
-- RED regression: construct one canonical finite amplitude table on which the
-- exact powMod permutation and literal cyclic phase transform are both defined.
------------------------------------------------------------------------

vectorRegisterSurfaceExists :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Set
vectorRegisterSurfaceExists qNonZero nNonZero base A =
  Vector.FiniteVectorAmplitudeState qNonZero nNonZero base A

oracleIsConstructivelyInvolutive :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  (ψ : Vector.FiniteVectorAmplitudeState qNonZero nNonZero base A) →
  Vector.vectorOracleState qNonZero nNonZero base A
    (Vector.vectorOracleState qNonZero nNonZero base A ψ)
  ≡ ψ
oracleIsConstructivelyInvolutive = Vector.vectorOracleStateInvolutive
