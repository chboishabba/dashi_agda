module DASHI.Geometry.ProjectionDefectSplitForcesParallelogram where

-- Canonical bridge for the contraction -> quadratic route:
-- projection-defect split regime -> parallelogram -> quadratic emergence axioms.
--
-- This module is intentionally narrow: Stage-C closure code should depend on
-- this bridge rather than importing alternate quadratic emergence routes.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.Integer as Int
open import Data.Integer.Properties as IntP
import Relation.Binary.Reasoning.Setoid as EqR

open import DASHI.Geometry.ProjectionDefect as PD
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.QuadraticFormEmergence as QFE
open import DASHI.Geometry.ProjectionDefectToParallelogram as PDP
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.QuadraticPolarization as QP

module ℤReason = EqR IntP.≡-setoid
open ℤReason

projectionDefectSplitForcesParallelogram :
  ∀ {m : Nat} →
  ∀ x y →
    QF.ScalarField._+s_ QES.ScalarFieldℤ
      (QP.Q̂core (PD.Additive._+_ (QES.AdditiveVecℤ {m}) x y))
      (QP.Q̂core
        (PD.Additive._+_ (QES.AdditiveVecℤ {m}) x
          (PD.Additive.-_ (QES.AdditiveVecℤ {m}) y)))
    ≡
    QF.ScalarField._+s_ QES.ScalarFieldℤ
      (QF.ScalarField._+s_ QES.ScalarFieldℤ (QP.Q̂core x) (QP.Q̂core x))
      (QF.ScalarField._+s_ QES.ScalarFieldℤ (QP.Q̂core y) (QP.Q̂core y))
projectionDefectSplitForcesParallelogram {m} =
  QES.parallelogramQ̂core {m}

projectionDefectOrthogonalAdditivity :
  ∀ {m : Nat} →
  ∀ x y →
  PD.ProjectionDefect.Orth (QES.PDzero {m}) x y →
  QP.Q̂core (PD.Additive._+_ (QES.AdditiveVecℤ {m}) x y)
    ≡
  QF.ScalarField._+s_ QES.ScalarFieldℤ (QP.Q̂core x) (QP.Q̂core y)
projectionDefectOrthogonalAdditivity {m} x y orth =
  begin
    QP.Q̂core (PD.Additive._+_ (QES.AdditiveVecℤ {m}) x y)
  ≡⟨ cong (λ t → QP.Q̂core (PD.Additive._+_ (QES.AdditiveVecℤ {m}) t y)) orth ⟩
    QP.Q̂core (PD.Additive._+_ (QES.AdditiveVecℤ {m}) (QP.zeroVecℤ {m}) y)
  ≡⟨ cong QP.Q̂core (QP.zeroVecℤ+ᵥ y) ⟩
    QP.Q̂core y
  ≡⟨ sym (IntP.+-identityˡ (QP.Q̂core y)) ⟩
    (Int.+ 0) Int.+ QP.Q̂core y
  ≡⟨ cong (λ t → Int._+_ t (QP.Q̂core y)) (sym (QES.Q̂core-zeroVec {m})) ⟩
    QP.Q̂core (QP.zeroVecℤ {m}) Int.+ QP.Q̂core y
  ≡⟨ sym (cong (λ t → Int._+_ t (QP.Q̂core y)) (cong QP.Q̂core orth)) ⟩
    QP.Q̂core x Int.+ QP.Q̂core y
  ∎

projectionDefectEnergySplit :
  ∀ {m : Nat} →
  ∀ x →
  QP.Q̂core x
    ≡
  QF.ScalarField._+s_ QES.ScalarFieldℤ
    (QP.Q̂core (PD.ProjectionDefect.P (QES.PDzero {m}) x))
    (QP.Q̂core (PD.ProjectionDefect.D (QES.PDzero {m}) x))
projectionDefectEnergySplit {m} x =
  begin
    QP.Q̂core x
  ≡⟨ sym (IntP.+-identityˡ (QP.Q̂core x)) ⟩
    (Int.+ 0) Int.+ QP.Q̂core x
  ≡⟨ cong (λ t → Int._+_ t (QP.Q̂core x)) (sym (QES.Q̂core-zeroVec {m})) ⟩
    QF.ScalarField._+s_ QES.ScalarFieldℤ
      (QP.Q̂core (PD.ProjectionDefect.P (QES.PDzero {m}) x))
      (QP.Q̂core (PD.ProjectionDefect.D (QES.PDzero {m}) x))
  ∎

quadraticEmergenceFromProjectionDefectSplit :
  ∀ {m : Nat} →
  QFE.QuadraticEmergenceAxioms
    (QES.AdditiveVecℤ {m})
    QES.ScalarFieldℤ
    (QES.PDzero {m})
quadraticEmergenceFromProjectionDefectSplit {m} =
  record
    { Energy = QP.Q̂core
    ; ParallelogramQ = projectionDefectSplitForcesParallelogram {m}
    ; Additive-On-Orth = projectionDefectOrthogonalAdditivity {m}
    ; PD-splits = projectionDefectEnergySplit {m}
    }

projectionDefectParallelogramFromSplit :
  ∀ {m : Nat} →
  PDP.ProjectionDefectParallelogramPackage
    (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ
projectionDefectParallelogramFromSplit {m} =
  PDP.fromEmergenceAxioms
    (QES.AdditiveVecℤ {m})
    QES.ScalarFieldℤ
    (QES.PDzero {m})
    (quadraticEmergenceFromProjectionDefectSplit {m})
