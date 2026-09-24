module DASHI.Crypto.ShorReversiblePowModOracleWeldRegression where

open import DASHI.Core.Prelude

import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.GeneralShor as Shor
import DASHI.Crypto.ShorOrderFinding as Order
import DASHI.Crypto.ShorReversiblePowModOracleWeldExact as Weld

------------------------------------------------------------------------
-- RED regression: the reversible graph oracle and the hidden-period oracle
-- must be the same arithmetic observable at every encoded finite basis point.
------------------------------------------------------------------------

sameOracleValue :
  ∀ {N a r} →
  (P : Order.ModularOrderProblem N a r) →
  (B : Finite.FiniteBasis) →
  (b : Finite.Basis B) →
  Weld.reversiblePowModValue P B b
  ≡
  Shor.oracle (Order.asHiddenPeriodProblem P) (Finite.encode B b)
sameOracleValue = Weld.reversiblePowModValueIsHiddenPeriodOracle
