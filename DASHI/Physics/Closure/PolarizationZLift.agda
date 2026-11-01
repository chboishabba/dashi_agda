module DASHI.Physics.Closure.PolarizationZLift where

open import Agda.Builtin.Nat using (Nat)
open import Data.Integer using (ℤ; +_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Geometry.OrthogonalityFromPolarization as OP
open import DASHI.Physics.QuadraticPolarization as QP
open import DASHI.Physics.QuadraticPolarizationCoreInstance as QPCI
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES

-- Polarization on the ℤ-lifted carrier using the same Qcore/dot.
polarizationZLift :
  ∀ {m : Nat} →
  OP.Polarization (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
polarizationZLift {m} =
  record
    { Q = QP.Q̂core
    ; ⟪_,_⟫ = QP.dotℤ
    ; two = + 2
    ; two-def = refl
    ; polarization = QPCI.polarization-core {m}
    }
