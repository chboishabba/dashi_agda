module DASHI.Algebra.TriadicFiniteIrrep where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Foundations.TriadicFiniteQuotient as Q

------------------------------------------------------------------------
-- Equality helper.

sym :
  ∀ {A : Set} {x y : A} →
  x ≡ y →
  y ≡ x
sym refl = refl

------------------------------------------------------------------------
-- Finite additive group structure on the exact depth-n quotient.
--
-- The carrier is already concrete.  Carry arithmetic and its group laws are
-- supplied by an instance so that no accidental digitwise-addition theorem is
-- promoted as arithmetic modulo 3^n.

record FiniteAdditiveGroup (n : Nat) : Set₁ where
  field
    zeroᵍ : Q.Residue3Pow n
    _+ᵍ_ :
      Q.Residue3Pow n →
      Q.Residue3Pow n →
      Q.Residue3Pow n
    negateᵍ : Q.Residue3Pow n → Q.Residue3Pow n

    leftIdentityᵍ :
      (x : Q.Residue3Pow n) →
      zeroᵍ +ᵍ x ≡ x

    associativityᵍ :
      (x y z : Q.Residue3Pow n) →
      (x +ᵍ y) +ᵍ z ≡ x +ᵍ (y +ᵍ z)

    leftInverseᵍ :
      (x : Q.Residue3Pow n) →
      negateᵍ x +ᵍ x ≡ zeroᵍ

    commutativeᵍ :
      (x y : Q.Residue3Pow n) →
      x +ᵍ y ≡ y +ᵍ x

open FiniteAdditiveGroup public

------------------------------------------------------------------------
-- Cyclotomic/phase target used by one-dimensional irreducible characters.

record PhaseRing : Set₁ where
  field
    Phase : Set
    oneᵖ : Phase
    _∙ᵖ_ : Phase → Phase → Phase
    conjugateᵖ : Phase → Phase

    oneMultiplyOne : oneᵖ ∙ᵖ oneᵖ ≡ oneᵖ
    phaseAssociative :
      (a b c : Phase) →
      (a ∙ᵖ b) ∙ᵖ c ≡ a ∙ᵖ (b ∙ᵖ c)

open PhaseRing public

record AdditiveCharacter
  {n : Nat}
  (G : FiniteAdditiveGroup n)
  (P : PhaseRing) : Set₁ where
  field
    frequency : Q.Residue3Pow n
    evaluate : Q.Residue3Pow n → Phase P

    evaluateZero : evaluate (zeroᵍ G) ≡ oneᵖ P

    additiveLaw :
      (x y : Q.Residue3Pow n) →
      evaluate (_+ᵍ_ G x y)
      ≡ _∙ᵖ_ P (evaluate x) (evaluate y)

open AdditiveCharacter public

------------------------------------------------------------------------
-- Exact signal/spectrum codec.

Signal : Nat → Set → Set
Signal n Coeff = Q.Residue3Pow n → Coeff

record ExactSpectralCodec (n : Nat) : Set₁ where
  field
    Coeff : Set
    Spectrum : Set

    analyze : Signal n Coeff → Spectrum
    synthesize : Spectrum → Signal n Coeff

    reconstructAnalyze :
      (f : Signal n Coeff) →
      (x : Q.Residue3Pow n) →
      synthesize (analyze f) x ≡ f x

    spectralWidth : Nat
    spectralWidthMatchesQuotient :
      spectralWidth ≡ Q.pow3 n

open ExactSpectralCodec public

-- The identity codec is an exact fallback and a useful regression baseline.
-- A character/Fourier implementation refines Spectrum without changing the
-- reconstruction contract.

identitySpectralCodec :
  (n : Nat) →
  (A : Set) →
  ExactSpectralCodec n
identitySpectralCodec n A =
  record
    { Coeff = A
    ; Spectrum = Signal n A
    ; analyze = λ f → f
    ; synthesize = λ f → f
    ; reconstructAnalyze = λ f x → refl
    ; spectralWidth = Q.pow3 n
    ; spectralWidthMatchesQuotient = refl
    }

------------------------------------------------------------------------
-- Translation action, invariant kernels, and irreducible block assembly.

translate :
  ∀ {n : Nat} {A : Set} →
  FiniteAdditiveGroup n →
  Q.Residue3Pow n →
  Signal n A →
  Signal n A
translate G a f x = f (_+ᵍ_ G x a)

record TranslationInvariantKernel
  {n : Nat}
  (G : FiniteAdditiveGroup n) : Set₁ where
  field
    Coeff : Set
    applyKernel : Signal n Coeff → Signal n Coeff

    translationCommutation :
      (a : Q.Residue3Pow n) →
      (f : Signal n Coeff) →
      (x : Q.Residue3Pow n) →
      applyKernel (translate G a f) x
      ≡ translate G a (applyKernel f) x

open TranslationInvariantKernel public

record IrrepBlockDecomposition
  {n : Nat}
  (G : FiniteAdditiveGroup n)
  (K : TranslationInvariantKernel G) : Set₁ where
  field
    Sector : Set
    Block : Sector → Set

    analyzeBlocks :
      Signal n (TranslationInvariantKernel.Coeff K) →
      (s : Sector) →
      Block s

    synthesizeBlocks :
      ((s : Sector) → Block s) →
      Signal n (TranslationInvariantKernel.Coeff K)

    blockReconstruction :
      (f : Signal n (TranslationInvariantKernel.Coeff K)) →
      (x : Q.Residue3Pow n) →
      synthesizeBlocks (analyzeBlocks f) x ≡ f x

    kernelOnBlock :
      (s : Sector) →
      Block s →
      Block s

    kernelBlockCompatibility :
      (f : Signal n (TranslationInvariantKernel.Coeff K)) →
      (s : Sector) →
      analyzeBlocks (applyKernel K f) s
      ≡ kernelOnBlock s (analyzeBlocks f s)

    parsevalOrEnergyIdentity : Set
    spectralTailBound : Set

open IrrepBlockDecomposition public

------------------------------------------------------------------------
-- Full finite character model.

record FiniteCharacterTransform (n : Nat) : Set₁ where
  field
    additiveGroup : FiniteAdditiveGroup n
    phaseRing : PhaseRing
    character :
      Q.Residue3Pow n →
      AdditiveCharacter additiveGroup phaseRing

    codec : ExactSpectralCodec n
    characterOrthogonality : Set
    characterCompleteness : Set

open FiniteCharacterTransform public

------------------------------------------------------------------------
-- A checked trivial phase target.  It validates the character-law interface;
-- it is not claimed to be the full cyclotomic transform.

data UnitPhase : Set where
  unit-phase : UnitPhase

unitPhaseRing : PhaseRing
unitPhaseRing =
  record
    { Phase = UnitPhase
    ; oneᵖ = unit-phase
    ; _∙ᵖ_ = λ a b → unit-phase
    ; conjugateᵖ = λ a → unit-phase
    ; oneMultiplyOne = refl
    ; phaseAssociative = λ a b c → refl
    }

trivialCharacter :
  ∀ {n : Nat} →
  (G : FiniteAdditiveGroup n) →
  AdditiveCharacter G unitPhaseRing
trivialCharacter G =
  record
    { frequency = zeroᵍ G
    ; evaluate = λ x → unit-phase
    ; evaluateZero = refl
    ; additiveLaw = λ x y → refl
    }

------------------------------------------------------------------------
-- Explicit claim boundary.

irrepStatement : String
irrepStatement =
  "Finite additive characters and translation-invariant kernels are separated into typed group, phase, codec, and block-decomposition interfaces; exact reconstruction is required pointwise."

irrepBoundary : String
irrepBoundary =
  "The identity codec and trivial character are checked baselines only. A genuine cyclotomic DFT, character orthogonality, Parseval identity, and Schur diagonalization require a supplied FiniteCharacterTransform and IrrepBlockDecomposition."
