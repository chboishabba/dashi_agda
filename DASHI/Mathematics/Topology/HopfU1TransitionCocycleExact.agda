module DASHI.Mathematics.Topology.HopfU1TransitionCocycleExact where

-- Structural Hopf-chart transition theorem over the existing actual U(1)
-- group. The local sections, overlap coordinate and smoothness of the
-- complex Hopf fibration remain separate geometric obligations.
-- DASHI contribution: reusable exact U(1) cocycle laws.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; sym; cong)
import DASHI.Physics.Electromagnetism.U1SU2GroupTorusExact as U1

Phase = U1.U1TorusElement

transition : Phase → Phase → Phase
transition a b = U1.u1Multiply (U1.u1Inverse a) b

transitionReflexive : (a : Phase) →
  transition a a ≡ U1.u1Identity
transitionReflexive = U1.u1InverseLeft

transitionCocycle : (a b c : Phase) →
  U1.u1Multiply (transition a b) (transition b c)
    ≡ transition a c
transitionCocycle a b c =
  trans (sym (U1.u1MultiplyAssociative (U1.u1Inverse a) b
           (U1.u1Multiply (U1.u1Inverse b) c)))
        (trans
          (cong (U1.u1Multiply (U1.u1Inverse a))
            (sym (U1.u1MultiplyAssociative b (U1.u1Inverse b) c)))
          (trans
            (cong (λ x → U1.u1Multiply (U1.u1Inverse a) x)
              (trans
                (cong (λ x → U1.u1Multiply x c) (U1.u1InverseRight b))
                (U1.u1IdentityLeft c)))
            refl))

transitionInverse : (a b : Phase) →
  U1.u1Multiply (transition a b) (transition b a)
    ≡ U1.u1Identity
transitionInverse a b =
  trans (transitionCocycle a b a) (transitionReflexive a)
