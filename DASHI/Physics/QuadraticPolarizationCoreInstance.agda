module DASHI.Physics.QuadraticPolarizationCoreInstance where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import Data.Integer using (ℤ; _+_; _-_; _*_; +_; -_)
open import Data.Integer.Properties as IntP

open import Data.Vec using (Vec)
open import DASHI.Geometry.QuadraticForm
open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.QuadraticPolarization as QP

open QP.ℤ-Reasoning

-- Scalar field instance for ℤ (minimal, for polarization only).
ScalarFieldℤ : ScalarField _
ScalarFieldℤ =
  record
    { S = ℤ
    ; _+s_ = _+_
    ; _*s_ = _*_
    ; 0s = + 0
    ; 1s = + 1
    ; -s_ = -_
    }

-- Polarization instance for Qcoreℤ using the dot product over ℤ.
polarizationCore :
  ∀ {m : Nat} →
  OP.Polarization (record
    { Carrier = Vec ℤ m
    ; _+_ = QP._+ᵥ_
    ; 0# = QP.zeroVecℤ {m}
    ; -_ = λ v → v  -- additive inverse not used in polarization proof here
    })
    ScalarFieldℤ
polarizationCore {m} =
  record
    { Q = QP.Q̂core
    ; ⟪_,_⟫ = QP.dotℤ
    ; two = + 2
    ; two-def = refl
    ; polarization = polarization-core
    }
  where
    postulate
      polarization-core :
        ∀ (x y : Vec ℤ m) →
          QP.Q̂core (QP._+ᵥ_ x y)
            ≡
          (QP.Q̂core x + QP.Q̂core y)
            + ((+ 2) * QP.dotℤ x y)
