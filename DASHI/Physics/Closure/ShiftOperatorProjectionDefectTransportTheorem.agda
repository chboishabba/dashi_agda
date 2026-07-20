module DASHI.Physics.Closure.ShiftOperatorProjectionDefectTransportTheorem where

-- Exact transport theorem from the concrete ternary C/P/R hierarchy to the
-- additive projection-defect language used by quadratic emergence.
--
-- Metric contraction alone does not imply a parallelogram law.  The missing
-- data are made explicit here: an additive shadow of the ternary projection,
-- its idempotence, an orthogonality relation, and compatibility of Q-hat-core
-- with the projection/defect split.  Once these are supplied, the canonical
-- ProjectionDefectParallelogramPackage is derived rather than postulated.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Geometry.ProjectionDefect as PD
open import DASHI.Geometry.QuadraticForm as QF
open import DASHI.Geometry.QuadraticFormEmergence as QFE
open import DASHI.Geometry.ProjectionDefectToParallelogram as PDP
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Physics.QuadraticPolarization as QP
open import DASHI.Physics.Closure.PhysicsClosureCrossPollinationTheorem as PCP

record AdditiveShiftShadow (m k : Nat) : Setω where
  field
    operatorEvidence : PCP.ShiftOperatorDefectHierarchyEvidence m k

    shadowProjection :
      PD.Additive.Carrier (QES.AdditiveVecℤ {m + k}) →
      PD.Additive.Carrier (QES.AdditiveVecℤ {m + k})

    shadowProjectionIdempotent :
      ∀ x → shadowProjection (shadowProjection x) ≡ shadowProjection x

    shadowDefect :
      PD.Additive.Carrier (QES.AdditiveVecℤ {m + k}) →
      PD.Additive.Carrier (QES.AdditiveVecℤ {m + k})

    shadowDefectDefinition :
      ∀ x →
      shadowDefect x ≡
      PD.Additive._+_ (QES.AdditiveVecℤ {m + k}) x
        (PD.Additive.-_ (QES.AdditiveVecℤ {m + k})
          (shadowProjection x))

    Orth :
      PD.Additive.Carrier (QES.AdditiveVecℤ {m + k}) →
      PD.Additive.Carrier (QES.AdditiveVecℤ {m + k}) → Set

    projectionDefectOrthogonal :
      ∀ x → Orth (shadowProjection x) (shadowDefect x)

    orthogonalAdditivity :
      ∀ x y → Orth x y →
      QP.Q̂core
        (PD.Additive._+_ (QES.AdditiveVecℤ {m + k}) x y)
      ≡
      QF.ScalarField._+s_ QES.ScalarFieldℤ
        (QP.Q̂core x) (QP.Q̂core y)

    energySplit :
      ∀ x →
      QP.Q̂core x ≡
      QF.ScalarField._+s_ QES.ScalarFieldℤ
        (QP.Q̂core (shadowProjection x))
        (QP.Q̂core (shadowDefect x))

shadowProjectionDefect :
  ∀ {m k} → AdditiveShiftShadow m k →
  PD.ProjectionDefect (QES.AdditiveVecℤ {m + k})
shadowProjectionDefect shadow =
  record
    { P = AdditiveShiftShadow.shadowProjection shadow
    ; D = AdditiveShiftShadow.shadowDefect shadow
    ; D-def = AdditiveShiftShadow.shadowDefectDefinition shadow
    ; P-idem = AdditiveShiftShadow.shadowProjectionIdempotent shadow
    ; Orth = AdditiveShiftShadow.Orth shadow
    ; Orth-PD = AdditiveShiftShadow.projectionDefectOrthogonal shadow
    }

shiftShadowEmergenceAxioms :
  ∀ {m k} (shadow : AdditiveShiftShadow m k) →
  QFE.QuadraticEmergenceAxioms
    (QES.AdditiveVecℤ {m + k})
    QES.ScalarFieldℤ
    (shadowProjectionDefect shadow)
shiftShadowEmergenceAxioms {m} {k} shadow =
  record
    { Energy = QP.Q̂core
    ; Scale = QES.scaleVec
    ; ParallelogramQ = QES.parallelogramQ̂core {m + k}
    ; HomogeneousQ = QES.homQ̂core
    ; Additive-On-Orth = AdditiveShiftShadow.orthogonalAdditivity shadow
    ; PD-splits = AdditiveShiftShadow.energySplit shadow
    }

shiftOperatorForcesProjectionDefectParallelogram :
  ∀ {m k} → AdditiveShiftShadow m k →
  PDP.ProjectionDefectParallelogramPackage
    (QES.AdditiveVecℤ {m + k}) QES.ScalarFieldℤ
shiftOperatorForcesProjectionDefectParallelogram {m} {k} shadow =
  PDP.fromEmergenceAxioms
    (QES.AdditiveVecℤ {m + k})
    QES.ScalarFieldℤ
    (shadowProjectionDefect shadow)
    (shiftShadowEmergenceAxioms shadow)

record ShiftOperatorQuadraticDerivation (m k : Nat) : Setω where
  field
    additiveShadow : AdditiveShiftShadow m k

  projectionDefectPackage :
    PDP.ProjectionDefectParallelogramPackage
      (QES.AdditiveVecℤ {m + k}) QES.ScalarFieldℤ
  projectionDefectPackage =
    shiftOperatorForcesProjectionDefectParallelogram additiveShadow

  quadraticWitness :
    PDP.ProjectionDefectQuadraticWitness
      (QES.AdditiveVecℤ {m + k}) QES.ScalarFieldℤ
  quadraticWitness =
    PDP.fromProjectionPackageWitness
      (QES.AdditiveVecℤ {m + k})
      QES.ScalarFieldℤ
      projectionDefectPackage
