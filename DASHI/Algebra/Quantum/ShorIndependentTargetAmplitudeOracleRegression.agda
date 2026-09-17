module DASHI.Algebra.Quantum.ShorIndependentTargetAmplitudeOracleRegression where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.ShorReversiblePowModOracleExact as Graph
import DASHI.Algebra.Quantum.ShorAmplitudeExecutionPrefixExact as Prefix
import DASHI.Algebra.Quantum.ShorIndependentTargetAmplitudeOracleExact as Product

------------------------------------------------------------------------
-- RED regression.
--
-- A post-oracle Shor carrier must permit the exponent coordinate to change
-- while retaining the computed target value.  The exact graph carrier cannot
-- express such off-graph states, but an independent exponent x target carrier
-- can.  Its reversible oracle must still inhabit the existing amplitude weld.
------------------------------------------------------------------------

independentTargetOracleWeldExists :
  (Coefficient : Set) →
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Prefix.ShorAmplitudeOracleWeld
    B base modulus modulusNonZero
    (Product.independentTargetAmplitudeRegister
      Coefficient B base modulus modulusNonZero)
independentTargetOracleWeldExists = Product.independentTargetAmplitudeOracleWeld

qftCanRelabelExponentWithoutChangingTarget :
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  (source target : Finite.Basis B) →
  Product.IndependentTargetState B base modulus modulusNonZero
qftCanRelabelExponentWithoutChangingTarget B base modulus modulusNonZero source target =
  Product.relabelExponent
    target
    (Product.computedTargetState B base modulus modulusNonZero source)
