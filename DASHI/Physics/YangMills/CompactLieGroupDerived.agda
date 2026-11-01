module DASHI.Physics.YangMills.CompactLieGroupDerived where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieGroupCore

------------------------------------------------------------------------
-- Derived group theory.  These are ordinary consequences of the group laws;
-- no compactness, coordinates, matrices, or analysis are used.
------------------------------------------------------------------------

leftInverseUnique :
  ∀ {g : Level} {G : Set g} →
  (H : Group G) →
  ∀ {x} y →
  multiply H y x ≡ identity H →
  y ≡ inverse H x
leftInverseUnique H {x} y yx≡e =
  trans
    (sym (identityRight H y))
    (trans
      (cong (multiply H y) (sym (inverseRight H x)))
      (trans
        (sym (multiplyAssociative H y x (inverse H x)))
        (trans
          (cong (λ z → multiply H z (inverse H x)) yx≡e)
          (identityLeft H (inverse H x)))))

rightInverseUnique :
  ∀ {g : Level} {G : Set g} →
  (H : Group G) →
  ∀ {x} y →
  multiply H x y ≡ identity H →
  y ≡ inverse H x
rightInverseUnique H {x} y xy≡e =
  trans
    (sym (identityLeft H y))
    (trans
      (cong (λ z → multiply H z y) (sym (inverseLeft H x)))
      (trans
        (multiplyAssociative H (inverse H x) x y)
        (trans
          (cong (multiply H (inverse H x)) xy≡e)
          (identityRight H (inverse H x)))))

inverseInvolutive :
  ∀ {g : Level} {G : Set g} →
  (H : Group G) →
  ∀ x → inverse H (inverse H x) ≡ x
inverseInvolutive H x =
  sym (leftInverseUnique H x (inverseRight H x))

inverseIdentity :
  ∀ {g : Level} {G : Set g} →
  (H : Group G) →
  inverse H (identity H) ≡ identity H
inverseIdentity H =
  trans
    (sym (identityRight H (inverse H (identity H))))
    (inverseLeft H (identity H))

leftInverseAction :
  ∀ {g : Level} {G : Set g} →
  (H : Group G) →
  ∀ x y →
  multiply H (inverse H x) (multiply H x y) ≡ y
leftInverseAction H x y =
  trans
    (sym (multiplyAssociative H (inverse H x) x y))
    (trans
      (cong (λ z → multiply H z y) (inverseLeft H x))
      (identityLeft H y))

rightInverseAction :
  ∀ {g : Level} {G : Set g} →
  (H : Group G) →
  ∀ x y →
  multiply H (multiply H y x) (inverse H x) ≡ y
rightInverseAction H x y =
  trans
    (multiplyAssociative H y x (inverse H x))
    (trans
      (cong (multiply H y) (inverseRight H x))
      (identityRight H y))

cancelLeft :
  ∀ {g : Level} {G : Set g} →
  (H : Group G) →
  ∀ {x y z} →
  multiply H x y ≡ multiply H x z →
  y ≡ z
cancelLeft H {x} {y} {z} equality =
  trans
    (sym (leftInverseAction H x y))
    (trans
      (cong (multiply H (inverse H x)) equality)
      (leftInverseAction H x z))

cancelRight :
  ∀ {g : Level} {G : Set g} →
  (H : Group G) →
  ∀ {x y z} →
  multiply H y x ≡ multiply H z x →
  y ≡ z
cancelRight H {x} {y} {z} equality =
  trans
    (sym (rightInverseAction H x y))
    (trans
      (cong (λ value → multiply H value (inverse H x)) equality)
      (rightInverseAction H x z))

conjugate :
  ∀ {g : Level} {G : Set g} →
  Group G → G → G → G
conjugate H h x =
  multiply H (multiply H h x) (inverse H h)

conjugateIdentity :
  ∀ {g : Level} {G : Set g} →
  (H : Group G) →
  ∀ h → conjugate H h (identity H) ≡ identity H
conjugateIdentity H h =
  trans
    (cong (λ value → multiply H value (inverse H h)) (identityRight H h))
    (inverseRight H h)

------------------------------------------------------------------------
-- The cancellation pattern used by lattice gauge covariance.  It proves that
-- the gauge values at an internal path vertex disappear exactly.
------------------------------------------------------------------------

gaugeTelescope :
  ∀ {g : Level} {G : Set g} →
  (H : Group G) →
  ∀ gx gy gz u v →
  multiply H
    (multiply H (multiply H gx u) (inverse H gy))
    (multiply H (multiply H gy v) (inverse H gz))
  ≡
  multiply H
    (multiply H gx (multiply H u v))
    (inverse H gz)
gaugeTelescope H gx gy gz u v =
  trans
    (multiplyAssociative H
      (multiply H gx u)
      (inverse H gy)
      (multiply H (multiply H gy v) (inverse H gz)))
    (trans
      (cong (multiply H (multiply H gx u))
        (sym (multiplyAssociative H
          (inverse H gy)
          (multiply H gy v)
          (inverse H gz))))
      (trans
        (cong (multiply H (multiply H gx u))
          (cong (λ value → multiply H value (inverse H gz))
            (leftInverseAction H gy v)))
        (trans
          (sym (multiplyAssociative H
            (multiply H gx u)
            v
            (inverse H gz)))
          (cong (λ value → multiply H value (inverse H gz))
            (multiplyAssociative H gx u v)))))

conjugateProduct :
  ∀ {g : Level} {G : Set g} →
  (H : Group G) →
  ∀ h x y →
  conjugate H h (multiply H x y)
  ≡
  multiply H (conjugate H h x) (conjugate H h y)
conjugateProduct H h x y =
  sym (gaugeTelescope H h h h x y)

------------------------------------------------------------------------
-- Exact inverse-action laws for the abstract adjoint representation.
------------------------------------------------------------------------

adjointInverseLeft :
  ∀ {g a : Level} {G : Set g} {𝔤 : Set a} →
  (K : CompactSimpleLieGroup G 𝔤) →
  ∀ x X →
  Ad K (inverse (group K) x) (Ad K x X) ≡ X
adjointInverseLeft K x X =
  trans
    (sym (adjointProduct K (inverse (group K) x) x X))
    (trans
      (cong (λ value → Ad K value X) (inverseLeft (group K) x))
      (adjointIdentity K X))

adjointInverseRight :
  ∀ {g a : Level} {G : Set g} {𝔤 : Set a} →
  (K : CompactSimpleLieGroup G 𝔤) →
  ∀ x X →
  Ad K x (Ad K (inverse (group K) x) X) ≡ X
adjointInverseRight K x X =
  trans
    (sym (adjointProduct K x (inverse (group K) x) X))
    (trans
      (cong (λ value → Ad K value X) (inverseRight (group K) x))
      (adjointIdentity K X))
