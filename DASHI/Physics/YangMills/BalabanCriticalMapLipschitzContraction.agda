module DASHI.Physics.YangMills.BalabanCriticalMapLipschitzContraction where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.BalabanUniformResidualMajorant

record AssociativeOrderedProduct (Bound : Set) : Set₁ where
  field
    order : OrderedProduct Bound
    associative : ∀ a b c →
      multiply order (multiply order a b) c
      ≡ multiply order a (multiply order b c)

open AssociativeOrderedProduct public

------------------------------------------------------------------------
-- Quantitative critical-map estimate:
--
--   ||Phi x - Phi y|| <= C_G (L_N ||x-y||)
--   C_G L_N <= rho
--
-- implies the repository's finite contraction estimate at rho.
------------------------------------------------------------------------

criticalMapLipschitzToContraction :
  ∀ {State Bound : Set} →
  (product : AssociativeOrderedProduct Bound) →
  (Phi : State → State) →
  (distance : State → State → Bound) →
  (greenBound nonlinearLipschitz rho : Bound) →
  (∀ x y →
    LessEqual (order product)
      (distance (Phi x) (Phi y))
      (multiply (order product) greenBound
        (multiply (order product) nonlinearLipschitz (distance x y)))) →
  LessEqual (order product)
    (multiply (order product) greenBound nonlinearLipschitz)
    rho →
  ∀ x y →
  LessEqual (order product)
    (distance (Phi x) (Phi y))
    (multiply (order product) rho (distance x y))
criticalMapLipschitzToContraction
  product Phi distance greenBound nonlinearLipschitz rho local factor x y =
  transitive (order product)
    (subst
      (λ upper → LessEqual (order product) (distance (Phi x) (Phi y)) upper)
      (sym (associative product greenBound nonlinearLipschitz (distance x y)))
      (local x y))
    (monotoneFirst (order product) (distance x y) factor)
