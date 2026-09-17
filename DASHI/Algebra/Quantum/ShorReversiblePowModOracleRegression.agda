module DASHI.Algebra.Quantum.ShorReversiblePowModOracleRegression where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.ShorReversiblePowModOracleExact as Oracle

------------------------------------------------------------------------
-- RED regression: a finite-register reversible clean-ancilla oracle must
-- expose the exact RSA.powMod graph value on every prepared basis state.
------------------------------------------------------------------------

oracleCircuitExists :
  (B : Finite.FiniteBasis) →
  Finite.ReversibleCircuit
    (Oracle.powModGraphRegister B 2 15 B369.nonZero)
oracleCircuitExists B =
  Oracle.powModGraphCircuit B 2 15 B369.nonZero

preparedBasisLoadsExactPowMod :
  (B : Finite.FiniteBasis) →
  (b : Finite.Basis B) →
  Finite.run (Oracle.powModGraphCircuit B 2 15 B369.nonZero)
    (Finite.prepare (Oracle.powModGraphRegister B 2 15 B369.nonZero) b)
  ≡
  Oracle.loaded
    b
    (Oracle.powModAtBasis B 2 15 B369.nonZero b)
    refl
preparedBasisLoadsExactPowMod B b =
  Oracle.powModGraphRunPrepared B 2 15 B369.nonZero b
