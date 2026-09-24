module DASHI.Algebra.Quantum.ShorFiniteVectorExecutionPrefixRegression where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector
import DASHI.Algebra.Quantum.ShorFiniteVectorExecutionPrefixExact as Prefix

------------------------------------------------------------------------
-- RED regression: once inversion for the literal finite character sums is
-- supplied, the canonical Vec register must compile to the existing Shor
-- oracle+QFT execution prefix with an identity carrier weld.
------------------------------------------------------------------------

vectorPrefixCompiles :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Vector.VectorCyclicPhaseInversionAuthority A →
  Set
vectorPrefixCompiles qNonZero nNonZero base A I =
  Prefix.CompiledVectorPrefix qNonZero nNonZero base A I
