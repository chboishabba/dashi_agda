module DASHI.Algebra.Quantum.DASHIQuantumNormalForm where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- DASHI-normalized quantum programs.
--
-- Equivalent implementations are quotiented by operational behaviour.  The
-- normalizer chooses a representative whose honest DASHI complexity does not
-- exceed that of the input.  This is a normal-form advantage theorem surface,
-- not a claim of an unconditional quantum complexity-class separation.
------------------------------------------------------------------------

record QuantumProgramModel : Set₁ where
  field
    Program : Set
    Input : Set
    Output : Set

    run : Program → Input → Output
    complexity : Program → Nat
    defect : Program → Nat

open QuantumProgramModel public

OperationallyEquivalent :
  (M : QuantumProgramModel) →
  Program M →
  Program M →
  Set
OperationallyEquivalent M P Q = ∀ x → run M P x ≡ run M Q x

record DASHINormalizer (M : QuantumProgramModel) : Set₁ where
  field
    normalize : Program M → Program M

    sound : ∀ P → OperationallyEquivalent M (normalize P) P
    complexityNonincrease :
      ∀ P → complexity M (normalize P) ≤ complexity M P
    defectNonincrease :
      ∀ P → defect M (normalize P) ≤ defect M P
    idempotent : ∀ P → normalize (normalize P) ≡ normalize P

open DASHINormalizer public

record StrictNormalFormGain
    (M : QuantumProgramModel)
    (N : DASHINormalizer M) : Set₁ where
  field
    witness : Program M
    complexityStrictlyDecreases :
      complexity M (normalize N witness) < complexity M witness

open StrictNormalFormGain public

-- The normalized representative remains interchangeable with the source
-- program for every input while carrying no greater declared cost or defect.
normal-form-correct :
  (M : QuantumProgramModel) →
  (N : DASHINormalizer M) →
  ∀ P x → run M (normalize N P) x ≡ run M P x
normal-form-correct M N P x = sound N P x
