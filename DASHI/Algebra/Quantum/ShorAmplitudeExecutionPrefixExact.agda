module DASHI.Algebra.Quantum.ShorAmplitudeExecutionPrefixExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Algebra.Quantum.ShorReversiblePowModOracleExact as Oracle
import DASHI.Algebra.Quantum.ShorCyclicQFTCarrierTransportExact as Fourier

------------------------------------------------------------------------
-- Q2 EXECUTION PREFIX: SAME AMPLITUDE REGISTER FOR ORACLE AND CYCLIC QFT
--
-- Q1 owns the exact reversible computational-basis graph action for RSA.powMod.
-- The cyclic DFT source owns Fourier inversion.  What must not be hidden is the
-- representation seam between those two objects.
--
-- `ShorAmplitudeOracleWeld` is exactly that seam: it embeds the Q1 graph state
-- into a supplied finite quantum register and requires the register's reversible
-- oracle action to intertwine with the exact graph action.  Clean computational
-- states are required to be the register's prepared basis states.
--
-- Once this weld and the independent cyclic-DFT carrier weld target the SAME
-- register, the oracle + QFT execution prefix is compiler output.  No amplitude
-- carrier, measurement law, sampling distribution, or continued-fraction
-- theorem is manufactured here.
------------------------------------------------------------------------

record ShorAmplitudeOracleWeld
    (B : Finite.FiniteBasis)
    (base modulus : Nat)
    (modulusNonZero : B369.NonZero modulus)
    (R : Finite.FiniteQuantumRegister B) : Set₁ where
  constructor shorAmplitudeOracleWeld
  field
    embedGraphState :
      Oracle.PowModGraphState B base modulus modulusNonZero →
      Finite.State R

    amplitudeOracle :
      Finite.ReversibleCircuit R

    cleanEmbedsAsPrepared :
      ∀ b →
      embedGraphState (Oracle.clean b)
      ≡ Finite.prepare R b

    oracleIntertwinesGraph :
      ∀ graphState →
      Finite.run amplitudeOracle (embedGraphState graphState)
      ≡ embedGraphState (Oracle.powModGraphStep graphState)

open ShorAmplitudeOracleWeld public

record ShorAmplitudeExecutionPrefix
    (B : Finite.FiniteBasis)
    (base modulus : Nat)
    (modulusNonZero : B369.NonZero modulus)
    (R : Finite.FiniteQuantumRegister B)
    {SourceState : Set}
    (sourceDFT : Fourier.CyclicDFTAction SourceState) : Set₁ where
  constructor shorAmplitudeExecutionPrefix
  field
    oracleWeld :
      ShorAmplitudeOracleWeld B base modulus modulusNonZero R

    fourierWeld :
      Fourier.CyclicQFTCarrierWeld R sourceDFT

    amplitudeOracleCircuit :
      Finite.ReversibleCircuit R

    amplitudeFourierTransform :
      QFT.FiniteFourierTransform R

    oracleCircuitIsWeldCircuit :
      amplitudeOracleCircuit ≡ amplitudeOracle oracleWeld

open ShorAmplitudeExecutionPrefix public

compileShorAmplitudeExecutionPrefix :
  ∀ {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero : B369.NonZero modulus}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {sourceDFT : Fourier.CyclicDFTAction SourceState} →
  ShorAmplitudeOracleWeld B base modulus modulusNonZero R →
  Fourier.CyclicQFTCarrierWeld R sourceDFT →
  ShorAmplitudeExecutionPrefix
    B base modulus modulusNonZero R sourceDFT
compileShorAmplitudeExecutionPrefix oracleWeld fourierWeld =
  shorAmplitudeExecutionPrefix
    oracleWeld
    fourierWeld
    (amplitudeOracle oracleWeld)
    (Fourier.transportCyclicDFTToFiniteQFT fourierWeld)
    refl

compiledPreparedOracleLoadsExactValue :
  ∀ {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero : B369.NonZero modulus}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {sourceDFT : Fourier.CyclicDFTAction SourceState} →
  (oracleWeld : ShorAmplitudeOracleWeld
    B base modulus modulusNonZero R) →
  (fourierWeld : Fourier.CyclicQFTCarrierWeld R sourceDFT) →
  (b : Finite.Basis B) →
  Finite.run
    (amplitudeOracleCircuit
      (compileShorAmplitudeExecutionPrefix oracleWeld fourierWeld))
    (Finite.prepare R b)
  ≡
  embedGraphState oracleWeld
    (Oracle.loaded
      b
      (Oracle.powModAtBasis B base modulus modulusNonZero b)
      refl)
compiledPreparedOracleLoadsExactValue oracleWeld fourierWeld b =
  trans
    (congRun (sym (cleanEmbedsAsPrepared oracleWeld b)))
    (oracleIntertwinesGraph oracleWeld (Oracle.clean b))
  where
    congRun :
      ∀ {x y} → x ≡ y →
      Finite.run (amplitudeOracle oracleWeld) x
      ≡ Finite.run (amplitudeOracle oracleWeld) y
    congRun refl = refl

compiledFourierIsTransportedSourceDFT :
  ∀ {B : Finite.FiniteBasis}
    {base modulus : Nat}
    {modulusNonZero : B369.NonZero modulus}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {sourceDFT : Fourier.CyclicDFTAction SourceState} →
  (oracleWeld : ShorAmplitudeOracleWeld
    B base modulus modulusNonZero R) →
  (fourierWeld : Fourier.CyclicQFTCarrierWeld R sourceDFT) →
  amplitudeFourierTransform
    (compileShorAmplitudeExecutionPrefix oracleWeld fourierWeld)
  ≡ Fourier.transportCyclicDFTToFiniteQFT fourierWeld
compiledFourierIsTransportedSourceDFT oracleWeld fourierWeld = refl

------------------------------------------------------------------------
-- Frontier / authority boundary.
------------------------------------------------------------------------

record ShorAmplitudeExecutionPrefixBoundary : Set where
  constructor shorAmplitudeExecutionPrefixBoundary
  field
    q1PowModGraphReused : Bool
    cyclicDFTTransportCompilerReused : Bool
    sameRegisterRequiredForOracleAndFourier : Bool
    amplitudeOracleWeldConstructedHere : Bool
    amplitudeSuperpositionCarrierConstructedHere : Bool
    measurementConstructedHere : Bool
    samplingDistributionConstructedHere : Bool
    periodRecoveryConstructedHere : Bool

canonicalShorAmplitudeExecutionPrefixBoundary :
  ShorAmplitudeExecutionPrefixBoundary
canonicalShorAmplitudeExecutionPrefixBoundary =
  shorAmplitudeExecutionPrefixBoundary
    true true true false false false false false
