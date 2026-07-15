module DASHI.Physics.Closure.NSTriadKNExactRingSolverBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Algebra.Bundles using (CommutativeRing)
open import Algebra.Structures using (IsAbelianGroup; IsGroup; IsMagma; IsMonoid; IsRing; IsCommutativeRing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import Data.Maybe.Base using (nothing)
import Tactic.RingSolver.Core.AlmostCommutativeRing as RingCore
import Tactic.RingSolver.NonReflective as RingSolver

open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNExactOrderedScalar as Scalar
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffInnerProduct as Algebra

------------------------------------------------------------------------
-- Adapter from DASHI's explicit finite-coordinate ring authority to the
-- standard library's bundled commutative-ring interface.  This is purely
-- structural: it adds no field-model assumption and lets polynomial
-- equalities be discharged by the standard ring normalizer.
------------------------------------------------------------------------

addInverseRight :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (a : Scalar.Scalar (Algebra.orderedScalar K)) →
  Scalar._+_ (Algebra.orderedScalar K) a
    (Scalar.neg (Algebra.orderedScalar K) a) ≡
  Scalar.zero (Algebra.orderedScalar K)
addInverseRight K a = trans
  (Algebra.addCommutative K a (Scalar.neg (Algebra.orderedScalar K) a))
  (Algebra.addInverseLeft K a)

mulOneRight :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (a : Scalar.Scalar (Algebra.orderedScalar K)) →
  Scalar._*_ (Algebra.orderedScalar K) a
    (Scalar.one (Algebra.orderedScalar K)) ≡ a
mulOneRight K a = trans
  (Algebra.mulCommutative K a (Scalar.one (Algebra.orderedScalar K)))
  (Algebra.mulOneLeft K a)

exactCommutativeRing :
  (K : Algebra.ExactOrderedCommutativeRing) → CommutativeRing _ _
exactCommutativeRing K = record
  { Carrier = Scalar.Scalar S
  ; _≈_ = _≡_
  ; _+_ = Scalar._+_ S
  ; _*_ = Scalar._*_ S
  ; -_ = Scalar.neg S
  ; 0# = Scalar.zero S
  ; 1# = Scalar.one S
  ; isCommutativeRing = record
    { isRing = record
      { +-isAbelianGroup = record
        { isGroup = record
          { isMonoid = record
            { isSemigroup = record
              { isMagma = record
                { isEquivalence = isEquivalence
                ; ∙-cong = cong₂ (Scalar._+_ S)
                }
              ; assoc = Algebra.addAssociative K
              }
            ; identity = Algebra.addZeroLeft K , Algebra.addZeroRight K
            }
          ; inverse = Algebra.addInverseLeft K , addInverseRight K
          ; ⁻¹-cong = cong (Scalar.neg S)
          }
        ; comm = Algebra.addCommutative K
        }
      ; *-cong = cong₂ (Scalar._*_ S)
      ; *-assoc = Algebra.mulAssociative K
      ; *-identity = Algebra.mulOneLeft K , mulOneRight K
      ; distrib = Algebra.mulDistributesOverAdditionRight K ,
                  (λ x y z → Algebra.mulDistributesOverAdditionLeft K y z x)
      }
    ; *-comm = Algebra.mulCommutative K
    }
  }
  where
  S = Algebra.orderedScalar K

private
  solverRing :
    (K : Algebra.ExactOrderedCommutativeRing) →
    RingCore.AlmostCommutativeRing _ _
  solverRing K = RingCore.fromCommutativeRing
    (exactCommutativeRing K) (λ _ → nothing)

module Solver (K : Algebra.ExactOrderedCommutativeRing) =
  RingSolver (solverRing K)

-- Smoke-test the adapter with a solver-generated theorem.  The weighted
-- transfer identity uses the same normalizer after conservation has removed
-- its dependent third transfer.
solverAddCommutative :
  (K : Algebra.ExactOrderedCommutativeRing) →
  (a b : Scalar.Scalar (Algebra.orderedScalar K)) →
  Scalar._+_ (Algebra.orderedScalar K) a b ≡
  Scalar._+_ (Algebra.orderedScalar K) b a
solverAddCommutative K =
  proof
  where
  module R = Solver K
  proof = R.solve 2 (λ a b → (a R.⊕ b) R.⊜ (b R.⊕ a)) refl
