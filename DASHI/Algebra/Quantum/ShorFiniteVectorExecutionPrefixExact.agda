module DASHI.Algebra.Quantum.ShorFiniteVectorExecutionPrefixExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.ShorCyclicQFTCarrierTransportExact as Fourier
import DASHI.Algebra.Quantum.ShorAmplitudeExecutionPrefixExact as Prefix
import DASHI.Algebra.Quantum.ShorCyclicExponentBasisExact as Cyclic
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteVectorAmplitudeRegisterExact as Vector

------------------------------------------------------------------------
-- PREFERRED SAME-REGISTER Q2 PREFIX ON CANONICAL FINITE VECTORS
--
-- The canonical nested-Vec register owns both:
--   * the constructive exact RSA.powMod target-coordinate permutation; and
--   * the literal cyclic character-sum Fourier action.
--
-- Once inversion of those exact finite sums is supplied, the source DFT state
-- is definitionally the register state and the carrier weld is identity.  The
-- repository's existing ShorAmplitudeExecutionPrefix is therefore compiler
-- output, with no residual amplitude-representation seam.
------------------------------------------------------------------------

VectorRegisterState :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Set
VectorRegisterState qNonZero nNonZero base A =
  Finite.State (Vector.vectorAmplitudeRegister qNonZero nNonZero base A)

vectorCyclicDFTAction :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Vector.VectorCyclicPhaseInversionAuthority A →
  Fourier.CyclicDFTAction
    (VectorRegisterState qNonZero nNonZero base A)
vectorCyclicDFTAction qNonZero nNonZero base A I = record
  { sourceForward = Vector.vectorForwardState A
  ; sourceInverse = Vector.vectorInverseState A
  ; sourceInverseAfterForward = inverseAfter
  ; sourceForwardAfterInverse = forwardAfter
  }
  where
    inverseAfter : ∀ ψ → Vector.vectorInverseState A (Vector.vectorForwardState A ψ) ≡ ψ
    inverseAfter (Vector.vectorAmplitudeState tag table)
      rewrite Vector.inverseAfterForwardTable I table = refl

    forwardAfter : ∀ ψ → Vector.vectorForwardState A (Vector.vectorInverseState A ψ) ≡ ψ
    forwardAfter (Vector.vectorAmplitudeState tag table)
      rewrite Vector.forwardAfterInverseTable I table = refl

vectorIdentityCarrierWeld :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  (I : Vector.VectorCyclicPhaseInversionAuthority A) →
  Fourier.CyclicQFTCarrierWeld
    (Vector.vectorAmplitudeRegister qNonZero nNonZero base A)
    (vectorCyclicDFTAction qNonZero nNonZero base A I)
vectorIdentityCarrierWeld qNonZero nNonZero base A I = record
  { toRegister = λ ψ → ψ
  ; fromRegister = λ ψ → ψ
  ; fromToRegister = λ ψ → refl
  ; toFromRegister = λ ψ → refl
  }

CompiledVectorPrefix :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Vector.VectorCyclicPhaseInversionAuthority A →
  Set
CompiledVectorPrefix {Q} {N} {Coefficient} qNonZero nNonZero base A I =
  Prefix.ShorAmplitudeExecutionPrefix
    (Cyclic.cyclicExponentBasis Q qNonZero)
    base N nNonZero
    (Vector.vectorAmplitudeRegister qNonZero nNonZero base A)
    (vectorCyclicDFTAction qNonZero nNonZero base A I)

compileFiniteVectorExecutionPrefix :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  (I : Vector.VectorCyclicPhaseInversionAuthority A) →
  CompiledVectorPrefix qNonZero nNonZero base A I
compileFiniteVectorExecutionPrefix qNonZero nNonZero base A I =
  Prefix.compileShorAmplitudeExecutionPrefix
    (Vector.vectorAmplitudeOracleWeld qNonZero nNonZero base A)
    (vectorIdentityCarrierWeld qNonZero nNonZero base A I)

compiledVectorPrefixCarrierWeldIsIdentity :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q)
    (I : Vector.VectorCyclicPhaseInversionAuthority A) →
  Prefix.fourierWeld
    (compileFiniteVectorExecutionPrefix qNonZero nNonZero base A I)
  ≡ vectorIdentityCarrierWeld qNonZero nNonZero base A I
compiledVectorPrefixCarrierWeldIsIdentity qNonZero nNonZero base A I = refl

record ShorFiniteVectorExecutionPrefixBoundary : Set where
  constructor shorFiniteVectorExecutionPrefixBoundary
  field
    canonicalFiniteVectorCarrierUsed : Bool
    oracleAndQFTSameObject : Bool
    q1GraphIntertwiningRetained : Bool
    literalCyclicCharacterTransformRetained : Bool
    carrierWeldIdentity : Bool
    functionExtensionalityNeeded : Bool
    coefficientFourierInversionStillRequired : Bool
    observationStillRequired : Bool
    probabilityStillRequired : Bool

canonicalShorFiniteVectorExecutionPrefixBoundary :
  ShorFiniteVectorExecutionPrefixBoundary
canonicalShorFiniteVectorExecutionPrefixBoundary =
  shorFiniteVectorExecutionPrefixBoundary
    true true true true true false true true true
