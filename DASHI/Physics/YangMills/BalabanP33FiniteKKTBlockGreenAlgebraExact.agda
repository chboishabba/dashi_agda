module DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockGreenAlgebraExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Franco Brezzi,
-- "On the Existence, Uniqueness and Approximation of Saddle-Point Problems
-- Arising from Lagrangian Multipliers",
-- RAIRO Analyse Numérique 8 (1974), 129--151.
-- No DOI was assigned to the cited article.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Construct the exact finite linear algebra consumed by the local saddle/KKT
-- solve. The state projector, Hessian, constraint and repair maps are proved
-- extensional and additive/subtractive before the block inverse is assembled.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT

record ConstrainedGreenData (Multiplier : Set) : Set₁ where
  field
    projectorData : KKT.FiniteKKTProjectorData Multiplier
    hessianMatrix : Matrix.RationalMatrix KKT.State
    green : KKT.StateVector → KKT.StateVector

    greenProjectFixed : ∀ source coordinate →
      KKT.selectedAdmissibleProject projectorData (green source) coordinate
      ≡ green source coordinate

    greenAfterProjectedHessian : ∀ vector coordinate →
      green
        (KKT.selectedAdmissibleProject projectorData
          (Rect.applyRectangular KKT.physicalStateCarrier hessianMatrix
            (KKT.selectedAdmissibleProject projectorData vector)))
        coordinate
      ≡ KKT.selectedAdmissibleProject projectorData vector coordinate

    projectedHessianAfterGreen : ∀ source coordinate →
      KKT.selectedAdmissibleProject projectorData
        (Rect.applyRectangular KKT.physicalStateCarrier hessianMatrix
          (KKT.selectedAdmissibleProject projectorData (green source)))
        coordinate
      ≡ KKT.selectedAdmissibleProject projectorData source coordinate

    greenZero : ∀ coordinate → green (λ _ → 0ℚ) coordinate ≡ 0ℚ

open ConstrainedGreenData public

hessianApply : ∀ {Multiplier} → ConstrainedGreenData Multiplier →
  KKT.StateVector → KKT.StateVector
hessianApply greenData = Rect.applyRectangular
  KKT.physicalStateCarrier (hessianMatrix greenData)

project : ∀ {Multiplier} → ConstrainedGreenData Multiplier →
  KKT.StateVector → KKT.StateVector
project greenData = KKT.selectedAdmissibleProject (projectorData greenData)

repair : ∀ {Multiplier} → ConstrainedGreenData Multiplier →
  KKT.StateVector → KKT.StateVector
repair greenData = KKT.selectedConstraintRepair (projectorData greenData)

projectPointwiseCong : ∀ {Multiplier}
    (greenData : ConstrainedGreenData Multiplier)
    {left right : KKT.StateVector} →
  (∀ coordinate → left coordinate ≡ right coordinate) →
  ∀ coordinate → project greenData left coordinate ≡ project greenData right coordinate
projectPointwiseCong greenData pointwise coordinate =
  let
    projector = projectorData greenData
    constraintCong = Rect.applyRectangularVectorCong
      KKT.physicalStateCarrier (KKT.constraintMatrix projector) pointwise
    greenCong = Rect.applyRectangularVectorCong
      (KKT.multiplierCarrier projector) (KKT.multiplierGreen projector)
      constraintCong
    repairCong = Rect.applyRectangularVectorCong
      (KKT.multiplierCarrier projector)
      (Rect.transposeRectangular (KKT.constraintMatrix projector))
      greenCong coordinate
  in cong₂ _-_ (pointwise coordinate) repairCong

hessianPointwiseCong : ∀ {Multiplier}
    (greenData : ConstrainedGreenData Multiplier)
    {left right : KKT.StateVector} →
  (∀ coordinate → left coordinate ≡ right coordinate) →
  ∀ coordinate → hessianApply greenData left coordinate
    ≡ hessianApply greenData right coordinate
hessianPointwiseCong greenData = Rect.applyRectangularVectorCong
  KKT.physicalStateCarrier (hessianMatrix greenData)

constraintAddExact : ∀ {Multiplier}
    (greenData : ConstrainedGreenData Multiplier) left right row →
  KKT.constraintApply (projectorData greenData)
    (Rect.vectorAdd left right) row
  ≡ KKT.constraintApply (projectorData greenData) left row
    + KKT.constraintApply (projectorData greenData) right row
constraintAddExact greenData = Rect.applyRectangularAdd
  KKT.physicalStateCarrier
  (KKT.constraintMatrix (projectorData greenData))

constraintSubtractExact : ∀ {Multiplier}
    (greenData : ConstrainedGreenData Multiplier) left right row →
  KKT.constraintApply (projectorData greenData)
    (Rect.vectorSubtract left right) row
  ≡ KKT.constraintApply (projectorData greenData) left row
    - KKT.constraintApply (projectorData greenData) right row
constraintSubtractExact greenData = Rect.applyRectangularSubtract
  KKT.physicalStateCarrier
  (KKT.constraintMatrix (projectorData greenData))

hessianAddExact : ∀ {Multiplier}
    (greenData : ConstrainedGreenData Multiplier) left right coordinate →
  hessianApply greenData (Rect.vectorAdd left right) coordinate
  ≡ hessianApply greenData left coordinate
    + hessianApply greenData right coordinate
hessianAddExact greenData = Rect.applyRectangularAdd
  KKT.physicalStateCarrier (hessianMatrix greenData)

hessianSubtractExact : ∀ {Multiplier}
    (greenData : ConstrainedGreenData Multiplier) left right coordinate →
  hessianApply greenData (Rect.vectorSubtract left right) coordinate
  ≡ hessianApply greenData left coordinate
    - hessianApply greenData right coordinate
hessianSubtractExact greenData = Rect.applyRectangularSubtract
  KKT.physicalStateCarrier (hessianMatrix greenData)

projectAddExact : ∀ {Multiplier}
    (greenData : ConstrainedGreenData Multiplier) left right coordinate →
  project greenData (Rect.vectorAdd left right) coordinate
  ≡ project greenData left coordinate + project greenData right coordinate
projectAddExact greenData left right coordinate =
  let
    projector = projectorData greenData
    constraintAdd : ∀ row →
      KKT.constraintApply projector (Rect.vectorAdd left right) row
      ≡ Rect.vectorAdd (KKT.constraintApply projector left)
          (KKT.constraintApply projector right) row
    constraintAdd row = constraintAddExact greenData left right row
    greenAdd : ∀ row →
      KKT.multiplierGreenApply projector
        (KKT.constraintApply projector (Rect.vectorAdd left right)) row
      ≡ Rect.vectorAdd
          (KKT.multiplierGreenApply projector
            (KKT.constraintApply projector left))
          (KKT.multiplierGreenApply projector
            (KKT.constraintApply projector right)) row
    greenAdd row = trans
      (Rect.applyRectangularVectorCong
        (KKT.multiplierCarrier projector)
        (KKT.multiplierGreen projector) constraintAdd row)
      (Rect.applyRectangularAdd (KKT.multiplierCarrier projector)
        (KKT.multiplierGreen projector)
        (KKT.constraintApply projector left)
        (KKT.constraintApply projector right) row)
    repairAdd = trans
      (Rect.applyRectangularVectorCong (KKT.multiplierCarrier projector)
        (Rect.transposeRectangular (KKT.constraintMatrix projector))
        greenAdd coordinate)
      (Rect.applyRectangularAdd (KKT.multiplierCarrier projector)
        (Rect.transposeRectangular (KKT.constraintMatrix projector))
        (KKT.multiplierGreenApply projector
          (KKT.constraintApply projector left))
        (KKT.multiplierGreenApply projector
          (KKT.constraintApply projector right))
        coordinate)
  in trans
    (cong ((left coordinate + right coordinate) -_) repairAdd)
    (ℚRing.solve-∀ (left coordinate) (right coordinate)
      (repair greenData left coordinate) (repair greenData right coordinate))

projectSubtractExact : ∀ {Multiplier}
    (greenData : ConstrainedGreenData Multiplier) left right coordinate →
  project greenData (Rect.vectorSubtract left right) coordinate
  ≡ project greenData left coordinate - project greenData right coordinate
projectSubtractExact greenData left right coordinate =
  let
    projector = projectorData greenData
    constraintSubtract : ∀ row →
      KKT.constraintApply projector (Rect.vectorSubtract left right) row
      ≡ Rect.vectorSubtract (KKT.constraintApply projector left)
          (KKT.constraintApply projector right) row
    constraintSubtract row = constraintSubtractExact greenData left right row
    greenSubtract : ∀ row →
      KKT.multiplierGreenApply projector
        (KKT.constraintApply projector (Rect.vectorSubtract left right)) row
      ≡ Rect.vectorSubtract
          (KKT.multiplierGreenApply projector
            (KKT.constraintApply projector left))
          (KKT.multiplierGreenApply projector
            (KKT.constraintApply projector right)) row
    greenSubtract row = trans
      (Rect.applyRectangularVectorCong
        (KKT.multiplierCarrier projector)
        (KKT.multiplierGreen projector) constraintSubtract row)
      (Rect.applyRectangularSubtract (KKT.multiplierCarrier projector)
        (KKT.multiplierGreen projector)
        (KKT.constraintApply projector left)
        (KKT.constraintApply projector right) row)
    repairSubtract = trans
      (Rect.applyRectangularVectorCong (KKT.multiplierCarrier projector)
        (Rect.transposeRectangular (KKT.constraintMatrix projector))
        greenSubtract coordinate)
      (Rect.applyRectangularSubtract (KKT.multiplierCarrier projector)
        (Rect.transposeRectangular (KKT.constraintMatrix projector))
        (KKT.multiplierGreenApply projector
          (KKT.constraintApply projector left))
        (KKT.multiplierGreenApply projector
          (KKT.constraintApply projector right))
        coordinate)
  in trans
    (cong ((left coordinate - right coordinate) -_) repairSubtract)
    (ℚRing.solve-∀ (left coordinate) (right coordinate)
      (repair greenData left coordinate) (repair greenData right coordinate))

finiteKKTBlockLinearityAlgebraLevel : ProofLevel
finiteKKTBlockLinearityAlgebraLevel = machineChecked
