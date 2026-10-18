module DASHI.Algebra.Quantum.ShorReversiblePowModOracleExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Crypto.RSAArithmeticCore as RSA
import DASHI.Core.OperatorTypes as Operator
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite

------------------------------------------------------------------------
-- REVERSIBLE CLEAN-ANCILLA GRAPH ORACLE FOR RSA.powMod
--
-- The existing finite-register layer needs only an invertible state action.
-- Rather than pretending the ordinary register machine is itself quantum, we
-- construct the exact reversible graph action for the arithmetic function used
-- by ShorOrderFinding:
--
--   clean |b,0>  <->  loaded |b, RSA.powMod a (encode b) N>.
--
-- The loaded constructor carries an equality proving that the recorded output
-- is literally the existing RSA.powMod observable.  This is a clean-ancilla
-- compute/uncompute carrier, not a claim about amplitudes, gate decomposition,
-- a dirty-target XOR/addition oracle, sampling distributions, or hardware.
------------------------------------------------------------------------

powModAtBasis :
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Finite.Basis B →
  Nat
powModAtBasis B base modulus modulusNonZero b =
  RSA.powMod
    base
    (Finite.encode B b)
    modulus
    {{modulusNonZero}}

data PowModGraphState
    (B : Finite.FiniteBasis)
    (base modulus : Nat)
    (modulusNonZero : B369.NonZero modulus) : Set where
  clean :
    (b : Finite.Basis B) →
    PowModGraphState B base modulus modulusNonZero

  loaded :
    (b : Finite.Basis B) →
    (value : Nat) →
    value ≡ powModAtBasis B base modulus modulusNonZero b →
    PowModGraphState B base modulus modulusNonZero

powModGraphStep :
  ∀ {B base modulus modulusNonZero} →
  PowModGraphState B base modulus modulusNonZero →
  PowModGraphState B base modulus modulusNonZero
powModGraphStep {B} {base} {modulus} {modulusNonZero} (clean b) =
  loaded
    b
    (powModAtBasis B base modulus modulusNonZero b)
    refl
powModGraphStep (loaded b value exact) = clean b

powModGraphStepInvolutive :
  ∀ {B base modulus modulusNonZero} →
  (s : PowModGraphState B base modulus modulusNonZero) →
  powModGraphStep (powModGraphStep s) ≡ s
powModGraphStepInvolutive (clean b) = refl
powModGraphStepInvolutive (loaded b value exact) rewrite exact = refl

powModGraphInvertible :
  ∀ {B base modulus modulusNonZero} →
  Operator.Invertible
    (powModGraphStep
      {B = B}
      {base = base}
      {modulus = modulus}
      {modulusNonZero = modulusNonZero})
powModGraphInvertible = record
  { inv = powModGraphStep
  ; left = powModGraphStepInvolutive
  ; right = powModGraphStepInvolutive
  }

powModGraphRegister :
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Finite.FiniteQuantumRegister B
powModGraphRegister B base modulus modulusNonZero = record
  { State = PowModGraphState B base modulus modulusNonZero
  ; prepare = clean
  ; observe = λ where
      (clean b) → b
      (loaded b value exact) → b
  ; observePrepared = λ b → refl
  }

powModGraphCircuit :
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  Finite.ReversibleCircuit
    (powModGraphRegister B base modulus modulusNonZero)
powModGraphCircuit B base modulus modulusNonZero = record
  { run = powModGraphStep
  ; reversible = powModGraphInvertible
  }

powModGraphRunPrepared :
  (B : Finite.FiniteBasis) →
  (base modulus : Nat) →
  (modulusNonZero : B369.NonZero modulus) →
  (b : Finite.Basis B) →
  Finite.run (powModGraphCircuit B base modulus modulusNonZero)
    (Finite.prepare (powModGraphRegister B base modulus modulusNonZero) b)
  ≡
  loaded
    b
    (powModAtBasis B base modulus modulusNonZero b)
    refl
powModGraphRunPrepared B base modulus modulusNonZero b = refl

------------------------------------------------------------------------
-- Authority boundary for Q1.
------------------------------------------------------------------------

record ShorPowModOracleBoundary : Set where
  constructor shorPowModOracleBoundary
  field
    exactRSApowModGraph : Bool
    reversibleCleanAncillaAction : Bool
    existingFiniteRegisterInterfaceReused : Bool
    dirtyTargetXorOracleClaimed : Bool
    amplitudeSemanticsClaimed : Bool
    gateDecompositionClaimed : Bool
    samplingDistributionClaimed : Bool
    physicalHardwareClaimed : Bool

canonicalShorPowModOracleBoundary : ShorPowModOracleBoundary
canonicalShorPowModOracleBoundary =
  shorPowModOracleBoundary
    true true true false false false false false
