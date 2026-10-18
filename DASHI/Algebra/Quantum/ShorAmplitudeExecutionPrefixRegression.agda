module DASHI.Algebra.Quantum.ShorAmplitudeExecutionPrefixRegression where

open import DASHI.Core.Prelude

import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.ShorReversiblePowModOracleExact as Oracle
import DASHI.Algebra.Quantum.ShorCyclicQFTCarrierTransportExact as Fourier
import DASHI.Algebra.Quantum.ShorAmplitudeExecutionPrefixExact as Prefix

------------------------------------------------------------------------
-- RED regression: exact amplitude-register/oracle and cyclic-DFT welds must
-- compile into one execution prefix on the same finite quantum register.
------------------------------------------------------------------------

prefixExists :
  ∀ {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {sourceDFT : Fourier.CyclicDFTAction SourceState} →
  Prefix.ShorAmplitudeOracleWeld
    B base modulus modulusNonZero R →
  Fourier.CyclicQFTCarrierWeld R sourceDFT →
  Prefix.ShorAmplitudeExecutionPrefix
    B base modulus modulusNonZero R sourceDFT
prefixExists = Prefix.compileShorAmplitudeExecutionPrefix

preparedOracleLoadsExactGraphValue :
  ∀ {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {sourceDFT : Fourier.CyclicDFTAction SourceState} →
  (oracleWeld : Prefix.ShorAmplitudeOracleWeld
    B base modulus modulusNonZero R) →
  (fourierWeld : Fourier.CyclicQFTCarrierWeld R sourceDFT) →
  (b : Finite.Basis B) →
  Finite.run
    (Prefix.amplitudeOracleCircuit
      (Prefix.compileShorAmplitudeExecutionPrefix oracleWeld fourierWeld))
    (Finite.prepare R b)
  ≡
  Prefix.embedGraphState oracleWeld
    (Oracle.loaded
      b
      (Oracle.powModAtBasis B base modulus modulusNonZero b)
      refl)
preparedOracleLoadsExactGraphValue oracleWeld fourierWeld b =
  Prefix.compiledPreparedOracleLoadsExactValue oracleWeld fourierWeld b
