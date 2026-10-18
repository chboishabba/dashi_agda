module DASHI.Algebra.Quantum.ShorScalarAmplitudeCarrierRegression where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.ShorReversiblePowModOracleExact as Graph
import DASHI.Algebra.Quantum.ShorAmplitudeExecutionPrefixExact as Prefix
import DASHI.Algebra.Quantum.ShorScalarAmplitudeCarrierExact as Scalar

------------------------------------------------------------------------
-- RED regression.
--
-- Q2's remaining Fourier seam needs scalar-labelled finite superpositions on
-- the SAME register that carries the exact Q1 powMod basis action.  The scalar
-- carrier stays abstract here; no complex, norm, Born, or QFT law is assumed.
------------------------------------------------------------------------

scalarAmplitudeOracleWeldExists :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Prefix.ShorAmplitudeOracleWeld
    B base modulus modulusNonZero
    (Scalar.scalarAmplitudeRegister Coefficient B base modulus modulusNonZero)
scalarAmplitudeOracleWeldExists = Scalar.scalarAmplitudeOracleWeld

scalarLabelsPreservedByOracle :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  (coefficient : Coefficient) →
  (g : Graph.PowModGraphState B base modulus modulusNonZero) →
  Finite.run
    (Prefix.amplitudeOracle
      (Scalar.scalarAmplitudeOracleWeld
        Coefficient B base modulus modulusNonZero))
    (Scalar.scalarWeight coefficient
      (Scalar.scalarBasisKet g))
  ≡
  Scalar.scalarWeight coefficient
    (Scalar.scalarBasisKet (Graph.powModGraphStep g))
scalarLabelsPreservedByOracle Coefficient B base modulus modulusNonZero coefficient g =
  Scalar.scalarAmplitudeOraclePreservesWeight
    Coefficient B base modulus modulusNonZero coefficient g
