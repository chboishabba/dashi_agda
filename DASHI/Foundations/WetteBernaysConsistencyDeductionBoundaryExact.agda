module DASHI.Foundations.WetteBernaysConsistencyDeductionBoundaryExact where

------------------------------------------------------------------------
-- WETTE / BERNAYS SOURCE CONTEXT
--
-- Paul Bernays,
-- "Zum Symposium ueber die Grundlagen der Mathematik",
-- Dialectica 25 (1971), 171--195.
-- DOI: 10.1111/j.1746-8361.1971.tb00598.x.
--
-- Bernays discusses Wette's programme and emphasizes the conditional form:
-- for a sufficiently expressive formal system, a proof inside the system of
-- its own consistency can be transformed into a contradiction inside that
-- system. This is not itself evidence that such an internal consistency proof
-- exists.
--
-- Eduard Wette,
-- "Vom Unendlichen zum Endlichen", Dialectica 24 (1970), 303--324.
-- DOI: 10.1111/j.1746-8361.1970.tb01221.x.
--
-- Eduard Wette,
-- "Contradiction within pure number theory because of a system-internal
-- 'consistency'-deduction", International Logic Review 5, no. 9 (1974),
-- 51--62.
--
-- DASHI CONTRIBUTION
--
-- Encode only the logical promotion boundary needed to audit Wette. The
-- Goedel/Bernays reduction is represented as an explicit supplied theorem.
-- The existence of a Wette proof of the internal consistency sentence is a
-- separate datum. No incompleteness theorem is reproved here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Abstract conditional reduction.
------------------------------------------------------------------------

record InternalConsistencyDeductionKernel : Set₁ where
  field
    Formula : Set
    Derivable : Formula → Set

    consistencySentence : Formula
    contradictionSentence : Formula

    internalConsistencyProofYieldsContradiction :
      Derivable consistencySentence →
      Derivable contradictionSentence

open InternalConsistencyDeductionKernel public

record InternalConsistencyProofClaim
  (kernel : InternalConsistencyDeductionKernel) : Set where
  constructor internalConsistencyProofClaim
  field
    proof : Derivable kernel (consistencySentence kernel)

open InternalConsistencyProofClaim public

deriveInternalContradiction :
  (kernel : InternalConsistencyDeductionKernel) →
  InternalConsistencyProofClaim kernel →
  Derivable kernel (contradictionSentence kernel)
deriveInternalContradiction kernel claim =
  internalConsistencyProofYieldsContradiction kernel (proof claim)

------------------------------------------------------------------------
-- Semantic reflection is another, stronger bridge.
--
-- If a metatheory additionally certifies that a derivation of the designated
-- contradiction is absurd, then an internal consistency proof claim plus the
-- conditional reduction is itself impossible in that metatheory.
------------------------------------------------------------------------

record ContradictionReflection
  (kernel : InternalConsistencyDeductionKernel) : Set₁ where
  field
    contradictionDerivationIsAbsurd :
      Derivable kernel (contradictionSentence kernel) → ⊥

open ContradictionReflection public

internalConsistencyProofClaimIsAbsurdUnderReflection :
  (kernel : InternalConsistencyDeductionKernel) →
  ContradictionReflection kernel →
  InternalConsistencyProofClaim kernel →
  ⊥
internalConsistencyProofClaimIsAbsurdUnderReflection kernel reflection claim =
  contradictionDerivationIsAbsurd reflection
    (deriveInternalContradiction kernel claim)

------------------------------------------------------------------------
-- Historical claim boundary.
------------------------------------------------------------------------

record WetteBernaysBoundary : Set where
  constructor wetteBernaysBoundary
  field
    conditionalConsistencyToContradictionInterfaceAvailable : Bool
    conditionalConsistencyToContradictionInterfaceAvailableIsTrue :
      conditionalConsistencyToContradictionInterfaceAvailable ≡ true

    wetteInternalConsistencyProofRecovered : Bool
    wetteInternalConsistencyProofRecoveredIsFalse :
      wetteInternalConsistencyProofRecovered ≡ false

    contradictionReflectionForOrdinaryArithmeticProved : Bool
    contradictionReflectionForOrdinaryArithmeticProvedIsFalse :
      contradictionReflectionForOrdinaryArithmeticProved ≡ false

    goedelSecondIncompletenessReprovedHere : Bool
    goedelSecondIncompletenessReprovedHereIsFalse :
      goedelSecondIncompletenessReprovedHere ≡ false

    ordinaryArithmeticInconsistencyEstablished : Bool
    ordinaryArithmeticInconsistencyEstablishedIsFalse :
      ordinaryArithmeticInconsistencyEstablished ≡ false

canonicalWetteBernaysBoundary : WetteBernaysBoundary
canonicalWetteBernaysBoundary =
  wetteBernaysBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
