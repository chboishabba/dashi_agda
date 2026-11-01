module DASHI.Algebra.Quantum.ShorCyclicExponentBasisRegression where

open import DASHI.Core.Prelude
open import Data.Fin.Base using (Fin)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.ShorCyclicExponentBasisExact as Cyclic

------------------------------------------------------------------------
-- RED regression: Shor's exponent register needs a literal Fin Q cyclic basis,
-- not merely an arbitrary finite basis with Nat encode/decode fields.
------------------------------------------------------------------------

cyclicBasisExists :
  (Q : Nat) →
  (qNonZero : B369.NonZero Q) →
  Finite.FiniteBasis
cyclicBasisExists = Cyclic.cyclicExponentBasis

cyclicAdditionExists :
  (Q : Nat) →
  (qNonZero : B369.NonZero Q) →
  Fin Q → Fin Q → Fin Q
cyclicAdditionExists = Cyclic.cyclicAdd
