module DASHI.Geometry.ClosestPoint where

open import Level using (Level; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; _,_)

open import DASHI.Core.Q using (ℚ; _+ℚ_; _-ℚ_; _*ℚ_; 0ℚ; 1ℚ; twoℚ)
open import Data.Rational using (_≤_)

record Quadratic (ℓ : Level) : Set (suc ℓ) where
  field
    V   : Set ℓ
    _+_ : V → V → V
    _-_ : V → V → V
    _·_ : ℚ → V → V
    Q   : V → ℚ
    Qpos : ∀ x → 0ℚ ≤ Q x
    Qhom : ∀ (a : ℚ) x → Q (a · x) ≡ (a *ℚ a) *ℚ Q x
    Qpara : ∀ x y →
      (Q (x + y) +ℚ Q (x - y)) ≡
      ((twoℚ *ℚ Q x) +ℚ (twoℚ *ℚ Q y))

record ProjectionOnto (ℓ : Level) (V : Set ℓ) : Set (suc ℓ) where
  field
    S   : V → Set ℓ
    P   : V → V
    PinS : ∀ x → S (P x)
    Pid : ∀ x → P (P x) ≡ P x

record ClosestPointAxioms (ℓ : Level) : Set (suc ℓ) where
  field
    Qd   : Quadratic ℓ
    Prj  : ProjectionOnto ℓ (Quadratic.V Qd)

  field
    -- Inner product via polarization (placeholder; you can supply the actual definition).
    ip : Quadratic.V Qd → Quadratic.V Qd → ℚ
    -- “Firm nonexpansive” in Q-geometry (inner product via polarization).
    -- This is the single seam from which ClosestPoint + Fejér follow.
    firm :
      ∀ x y →
        _≤_
          (Quadratic.Q Qd
            (Quadratic._-_ Qd (ProjectionOnto.P Prj x) (ProjectionOnto.P Prj y)))
          (ip
            (Quadratic._-_ Qd (ProjectionOnto.P Prj x) (ProjectionOnto.P Prj y))
            (Quadratic._-_ Qd x y))

  -- Provide ClosestPoint + Fejér monotonicity as axioms on this record.
  field
    closest :
      ∀ x → (∀ s → ProjectionOnto.S Prj s →
        _≤_
          (Quadratic.Q Qd (Quadratic._-_ Qd x (ProjectionOnto.P Prj x)))
          (Quadratic.Q Qd (Quadratic._-_ Qd x s)))

    fejer :
      ∀ x s → ProjectionOnto.S Prj s →
        _≤_
          (Quadratic.Q Qd (Quadratic._-_ Qd (ProjectionOnto.P Prj x) s))
          (Quadratic.Q Qd (Quadratic._-_ Qd x s))

ClosestPoint :
  ∀ {ℓ} → (A : ClosestPointAxioms ℓ) →
  let open ClosestPointAxioms A
  in
  ∀ x → (∀ s → ProjectionOnto.S Prj s →
    _≤_
      (Quadratic.Q Qd (Quadratic._-_ Qd x (ProjectionOnto.P Prj x)))
      (Quadratic.Q Qd (Quadratic._-_ Qd x s)))
ClosestPoint A = ClosestPointAxioms.closest A

FejerMonotone :
  ∀ {ℓ} → (A : ClosestPointAxioms ℓ) →
  let open ClosestPointAxioms A
  in
  ∀ x s → ProjectionOnto.S Prj s →
    _≤_
      (Quadratic.Q Qd (Quadratic._-_ Qd (ProjectionOnto.P Prj x) s))
      (Quadratic.Q Qd (Quadratic._-_ Qd x s))
FejerMonotone A = ClosestPointAxioms.fejer A

record EnergyDist (A : Set) : Set₁ where
  field
    E : A → A → Set

record ProxLike {A : Set} (ED : EnergyDist A) (P : A → A) (Fix : A → Set) : Set₁ where
  open EnergyDist ED
  field
    closest : ∀ x y → Fix y → E x (P x) → E x y
