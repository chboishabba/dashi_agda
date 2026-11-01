module DASHI.Physics.MaskedOperatorInvariants where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import Data.Vec using (Vec)
open import Data.Integer using (ℤ)

open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Physics.CanonicalizationMinimal as CM
open import DASHI.Physics.IndefiniteMaskQuadratic as IMQ
open import DASHI.Physics.LiftToFullState as LFS
open import DASHI.Physics.MaskedCanonicalizationInvariant as MCI
open import DASHI.Physics.TailCollapseProof as TCP

------------------------------------------------------------------------
-- The real shift/projection stack preserves the coarse masked geometry.

coreQσ-Rᵣ :
  ∀ {m k : Nat}
    (σ : Vec IMQ.Sign m)
    (x : Vec Trit (m + k)) →
  MCI.coreQσ σ (TCP.Rᵣ {m} {k} x) ≡ MCI.coreQσ σ x
coreQσ-Rᵣ {m} {k} σ x =
  cong (IMQ.Qσ σ) (LFS.coarse-invariant-R m k x)

coreQσ-Pᵣ :
  ∀ {m k : Nat}
    (σ : Vec IMQ.Sign m)
    (x : Vec Trit (m + k)) →
  MCI.coreQσ σ (TCP.Pᵣ {m} {k} x) ≡ MCI.coreQσ σ x
coreQσ-Pᵣ {m} {k} σ x =
  cong (IMQ.Qσ σ) (LFS.coarse-invariant-P m k x)

coreQσ-Tᵣ :
  ∀ {m k : Nat}
    (σ : Vec IMQ.Sign m)
    (x : Vec Trit (m + k)) →
  MCI.coreQσ σ (TCP.Tᵣ {m} {k} x) ≡ MCI.coreQσ σ x
coreQσ-Tᵣ {m} {k} σ x =
  cong (IMQ.Qσ σ) (LFS.coarse-invariant-T m k x)

coreQσ-Tᵣ-iterate :
  ∀ {m k : Nat}
    (σ : Vec IMQ.Sign m)
    (n : Nat)
    (x : Vec Trit (m + k)) →
  MCI.coreQσ σ (TCP.iterate n (TCP.Tᵣ {m} {k}) x)
    ≡ MCI.coreQσ σ x
coreQσ-Tᵣ-iterate {m} {k} σ n x =
  cong (IMQ.Qσ σ) (LFS.coarse-invariant-iter m k n x)

------------------------------------------------------------------------
-- Full closure step: canonicalize after scale shift and projection.

fullStep :
  ∀ {m k : Nat} → Vec Trit (m + k) → Vec Trit (m + k)
fullStep {m} {k} x = CM.Cᵣ {m} {k} (TCP.Tᵣ {m} {k} x)

coreQσ-fullStep :
  ∀ {m k : Nat}
    (σ : Vec IMQ.Sign m)
    (x : Vec Trit (m + k)) →
  MCI.coreQσ σ (fullStep {m} {k} x) ≡ MCI.coreQσ σ x
coreQσ-fullStep {m} {k} σ x =
  trans
    (MCI.coreQσ-Cᵣ σ (TCP.Tᵣ {m} {k} x))
    (coreQσ-Tᵣ σ x)

coreQσ-fullStep-iterate :
  ∀ {m k : Nat}
    (σ : Vec IMQ.Sign m)
    (n : Nat)
    (x : Vec Trit (m + k)) →
  MCI.coreQσ σ (TCP.iterate n (fullStep {m} {k}) x)
    ≡ MCI.coreQσ σ x
coreQσ-fullStep-iterate σ zero x = refl
coreQσ-fullStep-iterate {m} {k} σ (suc n) x =
  trans
    (coreQσ-fullStep-iterate σ n (fullStep {m} {k} x))
    (coreQσ-fullStep σ x)

------------------------------------------------------------------------
-- Bundle the earned operator/geometry compatibility.

record MaskedOperatorGeometry {m k : Nat}
  (σ : Vec IMQ.Sign m) : Set where
  field
    renormalization-invariant :
      ∀ x → MCI.coreQσ σ (TCP.Rᵣ {m} {k} x) ≡ MCI.coreQσ σ x

    projection-invariant :
      ∀ x → MCI.coreQσ σ (TCP.Pᵣ {m} {k} x) ≡ MCI.coreQσ σ x

    canonicalization-invariant :
      ∀ x → MCI.coreQσ σ (CM.Cᵣ {m} {k} x) ≡ MCI.coreQσ σ x

    full-step-invariant :
      ∀ x → MCI.coreQσ σ (fullStep {m} {k} x) ≡ MCI.coreQσ σ x

maskedOperatorGeometry :
  ∀ {m k : Nat} (σ : Vec IMQ.Sign m) →
  MaskedOperatorGeometry {m} {k} σ
maskedOperatorGeometry σ =
  record
    { renormalization-invariant = coreQσ-Rᵣ σ
    ; projection-invariant = coreQσ-Pᵣ σ
    ; canonicalization-invariant = MCI.coreQσ-Cᵣ σ
    ; full-step-invariant = coreQσ-fullStep σ
    }
