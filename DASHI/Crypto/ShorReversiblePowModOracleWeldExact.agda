module DASHI.Crypto.ShorReversiblePowModOracleWeldExact where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.GeneralShor as Shor
import DASHI.Algebra.Quantum.ShorReversiblePowModOracleExact as Oracle
import DASHI.Crypto.FiniteFactorArithmetic as Factor
import DASHI.Crypto.ShorOrderFinding as Order

------------------------------------------------------------------------
-- SAME-OBJECT WELD: REVERSIBLE RSA.powMod GRAPH <-> SHOR HIDDEN ORACLE
--
-- `asHiddenPeriodProblem` defines its oracle by the existing RSA.powMod
-- observable.  The reversible graph circuit does the same.  This owner fixes
-- the modulus witness to the exact-order certificate carried by the modular
-- order problem, so the equality below is definitional rather than a numerical
-- comparison performed after execution.
------------------------------------------------------------------------

orderModulusNonZero :
  ∀ {N a r} →
  Order.ModularOrderProblem N a r →
  B369.NonZero N
orderModulusNonZero P =
  Factor.modulusNonZero
    (Factor.periodCertificate (Order.exactOrder P))

reversiblePowModValue :
  ∀ {N a r} →
  Order.ModularOrderProblem N a r →
  (B : Finite.FiniteBasis) →
  Finite.Basis B →
  Nat
reversiblePowModValue {N} {a} P B b =
  Oracle.powModAtBasis
    B a N (orderModulusNonZero P) b

reversiblePowModValueIsHiddenPeriodOracle :
  ∀ {N a r} →
  (P : Order.ModularOrderProblem N a r) →
  (B : Finite.FiniteBasis) →
  (b : Finite.Basis B) →
  reversiblePowModValue P B b
  ≡
  Shor.oracle (Order.asHiddenPeriodProblem P) (Finite.encode B b)
reversiblePowModValueIsHiddenPeriodOracle P B b = refl

reversiblePowModCircuit :
  ∀ {N a r} →
  Order.ModularOrderProblem N a r →
  (B : Finite.FiniteBasis) →
  Finite.ReversibleCircuit
    (Oracle.powModGraphRegister
      B a N (orderModulusNonZero {N = N} {a = a} {r = r} P))
reversiblePowModCircuit {N} {a} {r} P B =
  Oracle.powModGraphCircuit
    B a N (orderModulusNonZero P)

reversiblePowModLoadsHiddenPeriodValue :
  ∀ {N a r} →
  (P : Order.ModularOrderProblem N a r) →
  (B : Finite.FiniteBasis) →
  (b : Finite.Basis B) →
  Finite.run (reversiblePowModCircuit P B)
    (Finite.prepare
      (Oracle.powModGraphRegister
        B a N (orderModulusNonZero {N = N} {a = a} {r = r} P))
      b)
  ≡
  Oracle.loaded
    b
    (Shor.oracle (Order.asHiddenPeriodProblem P) (Finite.encode B b))
    refl
reversiblePowModLoadsHiddenPeriodValue P B b = refl

------------------------------------------------------------------------
-- Boundary: this closes the arithmetic/object-identity part of Q1 only.
------------------------------------------------------------------------

record ShorPowModSameObjectBoundary : Set where
  constructor shorPowModSameObjectBoundary
  field
    reversibleGraphUsesRSApowMod : Bool
    hiddenPeriodUsesSameRSApowMod : Bool
    pointwiseSameObjectWeldClosed : Bool
    dirtyTargetOracleClosed : Bool
    coherentSuperpositionSemanticsClosed : Bool
    qftSamplingClosed : Bool

canonicalShorPowModSameObjectBoundary : ShorPowModSameObjectBoundary
canonicalShorPowModSameObjectBoundary =
  shorPowModSameObjectBoundary
    true true true false false false
