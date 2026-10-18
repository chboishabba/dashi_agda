module DASHI.Algebra.Quantum.ShorFreeAmplitudePowModOracleRegression where

open import DASHI.Core.Prelude

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.ShorReversiblePowModOracleExact as Graph
import DASHI.Algebra.Quantum.ShorAmplitudeExecutionPrefixExact as Prefix
import DASHI.Algebra.Quantum.ShorFreeAmplitudePowModOracleExact as Free

------------------------------------------------------------------------
-- RED regression.
--
-- The preferred Q2 route must have a genuine superposition syntax carrier on
-- which the exact Q1 powMod graph involution is lifted structurally.  The
-- result must inhabit the existing ShorAmplitudeOracleWeld rather than adding
-- a parallel oracle ontology.
------------------------------------------------------------------------

formalAmplitudeOracleWeldExists :
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Prefix.ShorAmplitudeOracleWeld
    B base modulus modulusNonZero
    (Free.freeAmplitudeRegister B base modulus modulusNonZero)
formalAmplitudeOracleWeldExists = Free.freeAmplitudeOracleWeld

preparedStateIsCleanBasisKet :
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  (b : Finite.Basis B) →
  Finite.prepare
    (Free.freeAmplitudeRegister B base modulus modulusNonZero)
    b
  ≡ Free.taggedAmplitude
      b
      (Free.basisKet (Graph.clean b))
preparedStateIsCleanBasisKet B base modulus modulusNonZero b = refl

oracleMapsEmbeddedBasisKetExactly :
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  (g : Graph.PowModGraphState B base modulus modulusNonZero) →
  Finite.run
    (Prefix.amplitudeOracle
      (Free.freeAmplitudeOracleWeld B base modulus modulusNonZero))
    (Free.embedGraphBasis B base modulus modulusNonZero g)
  ≡ Free.embedGraphBasis B base modulus modulusNonZero
      (Graph.powModGraphStep g)
oracleMapsEmbeddedBasisKetExactly B base modulus modulusNonZero g =
  Prefix.oracleIntertwinesGraph
    (Free.freeAmplitudeOracleWeld B base modulus modulusNonZero)
    g
