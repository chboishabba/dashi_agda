module DASHI.Algebra.Quantum.ShorFiniteSyntaxExecutionPrefixExact where

open import DASHI.Core.Prelude
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.ShorCyclicQFTCarrierTransportExact as Fourier
import DASHI.Algebra.Quantum.ShorAmplitudeExecutionPrefixExact as Prefix
import DASHI.Algebra.Quantum.ShorFiniteIndependentTargetAmplitudeOracleExact as Target
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase
import DASHI.Algebra.Quantum.ShorFiniteSyntaxCyclicPhaseQFTExact as SyntaxQFT

------------------------------------------------------------------------
-- SAME-REGISTER ORACLE + LITERAL CYCLIC-QFT PREFIX
--
-- The finite independent-target syntax register already owns a constructive
-- reversible lift of the exact RSA.powMod graph action.  The sibling QFT owner
-- defines the literal finite cyclic character expansion on the same state
-- syntax.  Once the exact character-sum inversion theorem is supplied, there
-- is no remaining representation transport:
--
--   source DFT state = register state
--   toRegister       = identity
--   fromRegister     = identity.
--
-- Therefore the existing `ShorAmplitudeExecutionPrefix` is compiler output.
-- The only remaining QFT-side authority is coefficient/root-of-unity algebra
-- strong enough to inhabit `SyntaxCyclicPhaseInversionAuthority`.
------------------------------------------------------------------------

SyntaxRegister :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat) →
  Set
SyntaxRegister {Q} {N} {Coefficient} qNonZero nNonZero base =
  Finite.State
    (Target.finiteIndependentTargetAmplitudeRegister
      Coefficient
      (SyntaxQFT.cyclicBasis qNonZero)
      base N nNonZero)

syntaxCyclicDFTAction :
  ∀ {Q N Coefficient base}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  SyntaxQFT.SyntaxCyclicPhaseInversionAuthority qNonZero nNonZero A →
  Fourier.CyclicDFTAction
    (SyntaxRegister {Coefficient = Coefficient} qNonZero nNonZero base)
syntaxCyclicDFTAction qNonZero nNonZero A I = record
  { sourceForward = SyntaxQFT.syntaxCyclicPhaseForward A
  ; sourceInverse = SyntaxQFT.syntaxCyclicPhaseInverse A
  ; sourceInverseAfterForward = SyntaxQFT.inverseAfterForward I
  ; sourceForwardAfterInverse = SyntaxQFT.forwardAfterInverse I
  }

syntaxIdentityCarrierWeld :
  ∀ {Q N Coefficient base}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  (I : SyntaxQFT.SyntaxCyclicPhaseInversionAuthority qNonZero nNonZero A) →
  Fourier.CyclicQFTCarrierWeld
    (Target.finiteIndependentTargetAmplitudeRegister
      Coefficient
      (SyntaxQFT.cyclicBasis qNonZero)
      base N nNonZero)
    (syntaxCyclicDFTAction qNonZero nNonZero A I)
syntaxIdentityCarrierWeld qNonZero nNonZero A I = record
  { toRegister = λ ψ → ψ
  ; fromRegister = λ ψ → ψ
  ; fromToRegister = λ ψ → refl
  ; toFromRegister = λ ψ → refl
  }

CompiledSyntaxPrefix :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  SyntaxQFT.SyntaxCyclicPhaseInversionAuthority qNonZero nNonZero A →
  Set
CompiledSyntaxPrefix {Q} {N} {Coefficient} qNonZero nNonZero base A I =
  Prefix.ShorAmplitudeExecutionPrefix
    (SyntaxQFT.cyclicBasis qNonZero)
    base N nNonZero
    (Target.finiteIndependentTargetAmplitudeRegister
      Coefficient
      (SyntaxQFT.cyclicBasis qNonZero)
      base N nNonZero)
    (syntaxCyclicDFTAction qNonZero nNonZero A I)

compileFiniteSyntaxExecutionPrefix :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  (I : SyntaxQFT.SyntaxCyclicPhaseInversionAuthority qNonZero nNonZero A) →
  CompiledSyntaxPrefix qNonZero nNonZero base A I
compileFiniteSyntaxExecutionPrefix {N = N} {Coefficient = Coefficient}
  qNonZero nNonZero base A I =
  Prefix.compileShorAmplitudeExecutionPrefix
    (Target.finiteIndependentTargetAmplitudeOracleWeld
      Coefficient
      (SyntaxQFT.cyclicBasis qNonZero)
      base N nNonZero)
    (syntaxIdentityCarrierWeld qNonZero nNonZero A I)

compiledPrefixUsesIdentityFourierCarrierWeld :
  ∀ {Q N Coefficient}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (base : Nat)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
    (I : SyntaxQFT.SyntaxCyclicPhaseInversionAuthority qNonZero nNonZero A) →
  Prefix.fourierWeld
    (compileFiniteSyntaxExecutionPrefix qNonZero nNonZero base A I)
  ≡ syntaxIdentityCarrierWeld qNonZero nNonZero A I
compiledPrefixUsesIdentityFourierCarrierWeld qNonZero nNonZero base A I = refl

record ShorFiniteSyntaxExecutionPrefixBoundary : Set where
  constructor shorFiniteSyntaxExecutionPrefixBoundary
  field
    powModOracleAndQFTUseSameRegister : Bool
    carrierWeldIsIdentity : Bool
    literalCharacterActionReused : Bool
    q1GraphIntertwiningReused : Bool
    coefficientInversionAuthorityStillRequired : Bool
    measurementStillRequired : Bool
    probabilityStillRequired : Bool

canonicalShorFiniteSyntaxExecutionPrefixBoundary :
  ShorFiniteSyntaxExecutionPrefixBoundary
canonicalShorFiniteSyntaxExecutionPrefixBoundary =
  shorFiniteSyntaxExecutionPrefixBoundary
    true true true true true true true
