module DASHI.Physics.YangMills.CompactLieInnerC3Exact where

------------------------------------------------------------------------
-- REUSE AND EXTEND EXISTING COMPACT-LIE GROUP CALCULUS
-- Original owner: CompactLieGroupCore.Group and CompactLieGroupDerived.
--
-- This is finite generic GROUP algebra, not an analytical Lie bracket,
-- an SU3 matrix implementation, or a new imported theorem socket.
-- In particular, a chosen element t of order dividing three induces
-- an inner action of order dividing three by Ad_t.
-- Nontriviality of Ad_t is a separate centre/faithfulness obligation.
--
-- New mathematical contribution is an Agda source-level presentation
-- of standard inverse-of-product, conjugation composition, and C3
-- inner-action consequences from the existing certified group axioms.
-- No analytic Gotô theorem is asserted here.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.YangMills.CompactLieGroupCore as Core
import DASHI.Physics.YangMills.CompactLieGroupDerived as Derived

inverseProduct :
  ∀ {g : Level} {G : Set g} →
  (H : Core.Group G) (a b : G) →
  Core.multiply H (Core.inverse H b) (Core.inverse H a)
    ≡ Core.inverse H (Core.multiply H a b)
inverseProduct H a b =
  Derived.leftInverseUnique H
    (Core.multiply H (Core.inverse H b) (Core.inverse H a))
    (trans
      (Core.multiplyAssociative H
        (Core.inverse H b) (Core.inverse H a) (Core.multiply H a b))
      (trans
        (cong (Core.multiply H (Core.inverse H b))
          (sym (Core.multiplyAssociative H (Core.inverse H a) a b)))
        (trans
          (cong (Core.multiply H (Core.inverse H b))
            (cong (λ x → Core.multiply H x b)
              (Core.inverseLeft H a)))
          (trans
            (cong (Core.multiply H (Core.inverse H b))
              (Core.identityLeft H b))
            (Core.inverseLeft H b)))))

conjugateByIdentity :
  ∀ {g : Level} {G : Set g} →
  (H : Core.Group G) (x : G) →
  Derived.conjugate H (Core.identity H) x ≡ x
conjugateByIdentity H x =
  trans
    (cong (λ z → Core.multiply H z (Core.inverse H (Core.identity H)))
      (Core.identityLeft H x))
    (trans
      (cong (Core.multiply H x) (Derived.inverseIdentity H))
      (Core.identityRight H x))

conjugateComposition :
  ∀ {g : Level} {G : Set g} →
  (H : Core.Group G) (a b x : G) →
  Derived.conjugate H a (Derived.conjugate H b x)
  ≡ Derived.conjugate H (Core.multiply H a b) x
conjugateComposition H a b x =
  trans
    (cong (λ z → Core.multiply H z (Core.inverse H a))
      (sym (Core.multiplyAssociative H
        a (Core.multiply H b x) (Core.inverse H b))))
    (trans
      (cong (λ z →
        Core.multiply H
          (Core.multiply H z (Core.inverse H b))
          (Core.inverse H a))
        (sym (Core.multiplyAssociative H a b x)))
      (trans
        (Core.multiplyAssociative H
          (Core.multiply H (Core.multiply H a b) x)
          (Core.inverse H b)
          (Core.inverse H a))
        (cong
          (Core.multiply H (Core.multiply H (Core.multiply H a b) x))
          (inverseProduct H a b))))

innerC3FromElementCube :
  ∀ {g : Level} {G : Set g} →
  (H : Core.Group G) (t : G) →
  Core.multiply H (Core.multiply H t t) t ≡ Core.identity H →
  (x : G) →
  Derived.conjugate H t
    (Derived.conjugate H t (Derived.conjugate H t x)) ≡ x
innerC3FromElementCube H t cube x =
  trans
    (conjugateComposition H t t (Derived.conjugate H t x))
    (trans
      (conjugateComposition H (Core.multiply H t t) t x)
      (trans
        (cong (λ g → Derived.conjugate H g x) cube)
        (conjugateByIdentity H x)))
