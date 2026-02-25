module DASHI.Geometry.ShiftIsotropyTailPerm where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; _++_; lookup; tabulate)
open import Data.Fin using (Fin)

open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Physics.TailCollapseProof using (coarseOf; tailOf)

------------------------------------------------------------------------
-- Tail permutations as lookup tables

Perm : Nat → Set
Perm k = Vec (Fin k) k

permuteVec : ∀ {A : Set} {k : Nat} → Perm k → Vec A k → Vec A k
permuteVec {A} {k} p xs = tabulate (λ i → lookup (lookup p i) xs)

------------------------------------------------------------------------
-- Tail action on full vectors: preserve coarse prefix, permute tail

actTailPerm : ∀ {m k : Nat} → Perm k → Vec Trit (m + k) → Vec Trit (m + k)
actTailPerm {m} {k} p x =
  coarseOf m k x ++ permuteVec p (tailOf m k x)

------------------------------------------------------------------------
-- Commutation lemma for composite T = C ∘ P ∘ R

commutesWithT-CPR :
  ∀ {m k : Nat}
  (R P C : Vec Trit (m + k) → Vec Trit (m + k))
  (p : Perm k) →
  (∀ x → R (actTailPerm {m} {k} p x) ≡ actTailPerm p (R x)) →
  (∀ x → P (actTailPerm {m} {k} p x) ≡ actTailPerm p (P x)) →
  (∀ x → C (actTailPerm {m} {k} p x) ≡ actTailPerm p (C x)) →
  (∀ x → C (P (R (actTailPerm {m} {k} p x))) ≡ actTailPerm p (C (P (R x))))
commutesWithT-CPR R P C p commR commP commC x =
  trans
    (cong (λ v → C (P v)) (commR x))
    (trans (cong (λ v → C v) (commP (R x)))
           (commC (P (R x))))
