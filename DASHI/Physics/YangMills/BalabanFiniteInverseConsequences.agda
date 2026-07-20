module DASHI.Physics.YangMills.BalabanFiniteInverseConsequences where

------------------------------------------------------------------------
-- Exact consequences of the finite Hessian/Green inverse certificate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.BalabanFiniteOneStepCore
open import DASHI.Physics.YangMills.CompactLieProofLevel

operatorInjective :
  ∀ {A : Set} →
  (certificate : FiniteInverseCertificate A) →
  ∀ {x y} → operator certificate x ≡ operator certificate y → x ≡ y
operatorInjective certificate {x} {y} equal =
  trans
    (sym (inverseLeft certificate x))
    (trans
      (cong (inverse certificate) equal)
      (inverseLeft certificate y))

inverseInjective :
  ∀ {A : Set} →
  (certificate : FiniteInverseCertificate A) →
  ∀ {x y} → inverse certificate x ≡ inverse certificate y → x ≡ y
inverseInjective certificate {x} {y} equal =
  trans
    (sym (inverseRight certificate x))
    (trans
      (cong (operator certificate) equal)
      (inverseRight certificate y))

inverseUnique :
  ∀ {A : Set} →
  (certificate : FiniteInverseCertificate A) →
  (candidate : A → A) →
  (candidateLeft : ∀ x → candidate (operator certificate x) ≡ x) →
  ∀ x → candidate x ≡ inverse certificate x
inverseUnique certificate candidate candidateLeft x =
  trans
    (cong candidate (sym (inverseRight certificate x)))
    (candidateLeft (inverse certificate x))

finiteInverseConsequencesLevel : ProofLevel
finiteInverseConsequencesLevel = machineChecked
