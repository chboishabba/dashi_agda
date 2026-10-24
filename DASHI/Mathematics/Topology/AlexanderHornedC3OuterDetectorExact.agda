module DASHI.Mathematics.Topology.AlexanderHornedC3OuterDetectorExact where

------------------------------------------------------------------------
-- EXACT EQUVARIANT FINITE-QUOTIENT OUTER-ACTION DETECTOR
--
-- A surjective equivariant quotient of an automorphism which is
-- non-inner on the quotient forces the original automorphism to be
-- non-inner.  Here the input group is the C3 meridian-group interface,
-- the intended quotient is A5 x A5 x A5, and the intended automorphism
-- cyclically permutes the three factors.
--
-- This module proves the implication; it does NOT instantiate the
-- target with a formal A5 or identify the source with geometric pi_1.
-- The finite A5 construction is separately audited in Python.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Mathematics.Topology.AlexanderHornedC3ExteriorBridge as Bridge

record EquivariantQuotientDetector
    (G : Bridge.EquivariantMeridianGroup) : Set₁ where
  field
    Quotient : Set
    quotientMultiply : Quotient → Quotient → Quotient
    quotientInverse : Quotient → Quotient
    quotientRotation : Quotient → Quotient

    project : Bridge.LoopClass G → Quotient
    -- A chosen lift is enough for this exact proof and is available for
    -- the finite intended quotient once a surjection is constructed.
    lift : Quotient → Bridge.LoopClass G
    liftExact : ∀ q → project (lift q) ≡ q

    projectMultiply : ∀ a b →
      project (Bridge.multiply G a b)
        ≡ quotientMultiply (project a) (project b)
    projectInverse : ∀ a →
      project (Bridge.invert G a)
        ≡ quotientInverse (project a)
    projectRotation : ∀ a →
      project (Bridge.rotateLoop G a)
        ≡ quotientRotation (project a)

    quotientRotationNotInner : ∀ q →
      (∀ y →
        quotientRotation y
        ≡ quotientMultiply (quotientMultiply q y) (quotientInverse q))
      → ⊥

open EquivariantQuotientDetector public

sourceInner : (G : Bridge.EquivariantMeridianGroup) →
  Bridge.LoopClass G → Bridge.LoopClass G → Bridge.LoopClass G
sourceInner G g x =
  Bridge.multiply G
    (Bridge.multiply G g x)
    (Bridge.invert G g)

targetInner : (G : Bridge.EquivariantMeridianGroup) →
  (Q : EquivariantQuotientDetector G) →
  Quotient Q → Quotient Q → Quotient Q
targetInner G Q g x =
  quotientMultiply Q
    (quotientMultiply Q g x)
    (quotientInverse Q g)

projectInner :
  (G : Bridge.EquivariantMeridianGroup) →
  (Q : EquivariantQuotientDetector G) →
  ∀ g x →
    project Q (sourceInner G g x)
    ≡ targetInner G Q (project Q g) (project Q x)
projectInner G Q g x =
  trans
    (projectMultiply Q
      (Bridge.multiply G g x)
      (Bridge.invert G g))
    (cong₂ (quotientMultiply Q)
      (projectMultiply Q g x)
      (projectInverse Q g))

innerActionDescends :
  (G : Bridge.EquivariantMeridianGroup) →
  (Q : EquivariantQuotientDetector G) →
  ∀ g →
  (∀ x → Bridge.rotateLoop G x ≡ sourceInner G g x) →
  ∀ y →
    quotientRotation Q y
    ≡ targetInner G Q (project Q g) y
innerActionDescends G Q g innerAtSource y =
  trans
    (cong (quotientRotation Q) (sym (liftExact Q y)))
    (trans
      (sym (projectRotation Q (lift Q y)))
      (trans
        (cong (project Q) (innerAtSource (lift Q y)))
        (trans
          (projectInner G Q g (lift Q y))
          (cong
            (targetInner G Q (project Q g))
            (liftExact Q y)))))

rotationCannotBeInnerIfDetectorExists :
  (G : Bridge.EquivariantMeridianGroup) →
  (Q : EquivariantQuotientDetector G) →
  ∀ g →
    (∀ x → Bridge.rotateLoop G x ≡ sourceInner G g x)
      → ⊥
rotationCannotBeInnerIfDetectorExists G Q g innerAtSource =
  quotientRotationNotInner Q (project Q g)
    (innerActionDescends G Q g innerAtSource)
