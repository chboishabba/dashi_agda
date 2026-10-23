module DASHI.Mathematics.Topology.AlexanderHornedC3FreeFactorDetectorExact where

------------------------------------------------------------------------
-- THREE HORNED FACTORS: OUTER ACTION DETECTED WITHOUT A5
--
-- ATTRIBUTION / SCOPE
-- Hatcher, Algebraic Topology, Example 2B.2, gives a nontrivial
-- Alexander exterior group and an injective free-group tower.
-- Van Kampen's free-product theorem supplies the gluing algebra.
-- This module proves the GROUP-THEORETIC detector using only a
-- retraction/projection to the first factor and group identities.
-- It does not assert that a geometric boundary connected sum has
-- already been identified with a group of this form.
--
-- If the C3 rotation sends one essential first-sector meridian into
-- another free factor, projecting to the first factor kills the
-- rotated meridian. Conjugation cannot kill a nonidentity element.
-- Therefore rotation is not inner. This bypasses A5 entirely.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Mathematics.Topology.AlexanderHornedC3ExteriorBridge as Bridge
import DASHI.Mathematics.Topology.AlexanderHornedC3OuterDetectorExact as Outer

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record TargetGroup : Set₁ where
  field
    Carrier : Set
    unit : Carrier
    product : Carrier → Carrier → Carrier
    inverse : Carrier → Carrier
    associative : ∀ a b c →
      product (product a b) c ≡ product a (product b c)
    leftIdentity : ∀ a → product unit a ≡ a
    rightIdentity : ∀ a → product a unit ≡ a
    leftInverse : ∀ a → product (inverse a) a ≡ unit
    rightInverse : ∀ a → product a (inverse a) ≡ unit

open TargetGroup public

cancelLeftInverse : (T : TargetGroup) → ∀ g x →
  product T (inverse T g) (product T g x) ≡ x
cancelLeftInverse T g x =
  trans
    (sym (associative T (inverse T g) g x))
    (trans
      (cong (λ z → product T z x) (leftInverse T g))
      (leftIdentity T x))

cancelRightInverse : (T : TargetGroup) → ∀ x g →
  product T (product T x (inverse T g)) g ≡ x
cancelRightInverse T x g =
  trans
    (associative T x (inverse T g) g)
    (trans
      (cong (product T x) (leftInverse T g))
      (rightIdentity T x))

-- Inner conjugation reflects the identity in any group.
conjugationCannotKill : (T : TargetGroup) → ∀ g x →
  product T (product T g x) (inverse T g) ≡ unit T →
  x ≡ unit T
conjugationCannotKill T g x conjugateUnit =
  trans
    (sym (cancelLeftInverse T g x))
    (trans
      (cong (product T (inverse T g))
        (trans
          (sym (cancelRightInverse T (product T g x) g))
          (trans
            (cong (λ z → product T z g) conjugateUnit)
            (leftIdentity T g))))
      (leftInverse T g))

record FreeFactorDetector
    (G : Bridge.EquivariantMeridianGroup) : Set₁ where
  field
    factor : TargetGroup
    project : Bridge.LoopClass G → Carrier factor
    projectMultiply : ∀ a b →
      project (Bridge.multiply G a b)
        ≡ product factor (project a) (project b)
    projectInverse : ∀ a →
      project (Bridge.invert G a)
        ≡ inverse factor (project a)
    chosenMeridian : Bridge.LoopClass G
    chosenIsEssential :
      project chosenMeridian ≢ unit factor
    cyclicRotationLeavesFirstFactor :
      project (Bridge.rotateLoop G chosenMeridian) ≡ unit factor

open FreeFactorDetector public

projectionPreservesConjugation :
  (G : Bridge.EquivariantMeridianGroup) →
  (D : FreeFactorDetector G) → ∀ g x →
    project D (Outer.sourceInner G g x)
    ≡ product (factor D)
        (product (factor D) (project D g) (project D x))
        (inverse (factor D) (project D g))
projectionPreservesConjugation G D g x =
  trans
    (projectMultiply D
      (Bridge.multiply G g x)
      (Bridge.invert G g))
    (cong₂ (product (factor D))
      (projectMultiply D g x)
      (projectInverse D g))

rotationCannotBeInnerByFreeFactors :
  (G : Bridge.EquivariantMeridianGroup) →
  (D : FreeFactorDetector G) → ∀ g →
  (∀ x →
    Bridge.rotateLoop G x ≡ Outer.sourceInner G g x) →
  ⊥
rotationCannotBeInnerByFreeFactors G D g hypotheticalInner =
  chosenIsEssential D
    (conjugationCannotKill
      (factor D)
      (project D g)
      (project D (chosenMeridian D))
      (trans
        (sym
          (projectionPreservesConjugation G D
            g (chosenMeridian D)))
        (trans
          (sym (cong (project D)
            (hypotheticalInner (chosenMeridian D))))
          (cyclicRotationLeavesFirstFactor D))))
