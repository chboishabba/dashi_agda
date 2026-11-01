module DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices",
-- Proceedings of the Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
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
-- DASHI CONTRIBUTION
--
-- Expose the KKT projector through a basis-independent Moore--Penrose surface.
-- Redundant multiplier rows are not deleted. Instead the Gram operator K=L L*
-- carries a certified pseudoinverse K+ and P=I-L* K+ L. From the action laws
-- we prove exact constraint repair, idempotence, self-adjointness, the
-- kernel/adjoint-range decomposition and the universal characterization:
-- P v is the unique w with L w=0 and v-w in im L*.
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

MultiplierVector : Set → Set
MultiplierVector Multiplier = Multiplier → ℚ

constraintGramRaw :
  ∀ {Multiplier : Set} →
  Matrix.FiniteRationalCoordinates Multiplier →
  Rect.RectangularMatrix Multiplier KKT.State →
  Matrix.RationalMatrix Multiplier
constraintGramRaw multiplierCarrier constraintMatrix =
  Rect.composeRectangular
    KKT.physicalStateCarrier constraintMatrix
    (Rect.transposeRectangular constraintMatrix)

record FiniteKKTPseudoinverseData (Multiplier : Set) : Set₁ where
  field
    multiplierCarrier : Matrix.FiniteRationalCoordinates Multiplier
    constraintMatrix : Rect.RectangularMatrix Multiplier KKT.State
    gramPseudoinverse : Matrix.RationalMatrix Multiplier
    gramPseudoinverseSymmetric : ∀ left right →
      gramPseudoinverse left right ≡ gramPseudoinverse right left

    gramPseudoGramAction : ∀ multiplier row →
      Rect.applyRectangular multiplierCarrier
        (constraintGramRaw multiplierCarrier constraintMatrix)
        (Rect.applyRectangular multiplierCarrier gramPseudoinverse
          (Rect.applyRectangular multiplierCarrier
            (constraintGramRaw multiplierCarrier constraintMatrix)
            multiplier)) row
      ≡ Rect.applyRectangular multiplierCarrier
          (constraintGramRaw multiplierCarrier constraintMatrix)
          multiplier row

    pseudoGramPseudoAction : ∀ multiplier row →
      Rect.applyRectangular multiplierCarrier gramPseudoinverse
        (Rect.applyRectangular multiplierCarrier
          (constraintGramRaw multiplierCarrier constraintMatrix)
          (Rect.applyRectangular multiplierCarrier gramPseudoinverse
            multiplier)) row
      ≡ Rect.applyRectangular multiplierCarrier gramPseudoinverse
          multiplier row

    gramPseudoSymmetric : ∀ left right →
      Rect.composeRectangular multiplierCarrier
        (constraintGramRaw multiplierCarrier constraintMatrix)
        gramPseudoinverse left right
      ≡ Rect.composeRectangular multiplierCarrier
          (constraintGramRaw multiplierCarrier constraintMatrix)
          gramPseudoinverse right left

    pseudoGramSymmetric : ∀ left right →
      Rect.composeRectangular multiplierCarrier gramPseudoinverse
        (constraintGramRaw multiplierCarrier constraintMatrix)
        left right
      ≡ Rect.composeRectangular multiplierCarrier gramPseudoinverse
          (constraintGramRaw multiplierCarrier constraintMatrix)
          right left

    gramPseudoFixesConstraintImage : ∀ state row →
      Rect.applyRectangular multiplierCarrier
        (constraintGramRaw multiplierCarrier constraintMatrix)
        (Rect.applyRectangular multiplierCarrier gramPseudoinverse
          (Rect.applyRectangular KKT.physicalStateCarrier
            constraintMatrix state)) row
      ≡ Rect.applyRectangular KKT.physicalStateCarrier
          constraintMatrix state row

    adjointPseudoGramFixesAdjointImage : ∀ multiplier coordinate →
      Rect.applyRectangular multiplierCarrier
        (Rect.transposeRectangular constraintMatrix)
        (Rect.applyRectangular multiplierCarrier gramPseudoinverse
          (Rect.applyRectangular multiplierCarrier
            (constraintGramRaw multiplierCarrier constraintMatrix)
            multiplier)) coordinate
      ≡ Rect.applyRectangular multiplierCarrier
          (Rect.transposeRectangular constraintMatrix)
          multiplier coordinate

open FiniteKKTPseudoinverseData public

constraintApply : ∀ {Multiplier} →
  FiniteKKTPseudoinverseData Multiplier →
  KKT.StateVector → MultiplierVector Multiplier
constraintApply pseudoData = Rect.applyRectangular
  KKT.physicalStateCarrier (constraintMatrix pseudoData)

constraintAdjointApply : ∀ {Multiplier} →
  FiniteKKTPseudoinverseData Multiplier →
  MultiplierVector Multiplier → KKT.StateVector
constraintAdjointApply pseudoData = Rect.applyRectangular
  (multiplierCarrier pseudoData)
  (Rect.transposeRectangular (constraintMatrix pseudoData))

constraintGram : ∀ {Multiplier} →
  FiniteKKTPseudoinverseData Multiplier → Matrix.RationalMatrix Multiplier
constraintGram pseudoData = constraintGramRaw
  (multiplierCarrier pseudoData) (constraintMatrix pseudoData)

gramApply : ∀ {Multiplier} →
  FiniteKKTPseudoinverseData Multiplier →
  MultiplierVector Multiplier → MultiplierVector Multiplier
gramApply pseudoData = Rect.applyRectangular
  (multiplierCarrier pseudoData) (constraintGram pseudoData)

pseudoApply : ∀ {Multiplier} →
  FiniteKKTPseudoinverseData Multiplier →
  MultiplierVector Multiplier → MultiplierVector Multiplier
pseudoApply pseudoData = Rect.applyRectangular
  (multiplierCarrier pseudoData) (gramPseudoinverse pseudoData)

constraintRepair : ∀ {Multiplier} →
  FiniteKKTPseudoinverseData Multiplier →
  KKT.StateVector → KKT.StateVector
constraintRepair pseudoData vector = constraintAdjointApply pseudoData
  (pseudoApply pseudoData (constraintApply pseudoData vector))

admissibleProject : ∀ {Multiplier} →
  FiniteKKTPseudoinverseData Multiplier →
  KKT.StateVector → KKT.StateVector
admissibleProject pseudoData vector =
  Rect.vectorSubtract vector (constraintRepair pseudoData vector)

record ConstraintKernel {Multiplier : Set}
    (pseudoData : FiniteKKTPseudoinverseData Multiplier)
    (vector : KKT.StateVector) : Set where
  field
    constraintZero : ∀ row → constraintApply pseudoData vector row ≡ 0ℚ
open ConstraintKernel public

record AdjointRange {Multiplier : Set}
    (pseudoData : FiniteKKTPseudoinverseData Multiplier)
    (vector : KKT.StateVector) : Set₁ where
  field
    multiplier : MultiplierVector Multiplier
    representedByAdjoint : ∀ coordinate →
      vector coordinate ≡ constraintAdjointApply pseudoData multiplier coordinate
open AdjointRange public

constraintGramActionExact : ∀ {Multiplier}
    (pseudoData : FiniteKKTPseudoinverseData Multiplier) multiplier row →
  constraintApply pseudoData (constraintAdjointApply pseudoData multiplier) row
  ≡ gramApply pseudoData multiplier row
constraintGramActionExact pseudoData multiplier row = sym
  (Rect.applyComposeRectangularExact
    KKT.physicalStateCarrier (multiplierCarrier pseudoData)
    (constraintMatrix pseudoData)
    (Rect.transposeRectangular (constraintMatrix pseudoData))
    multiplier row)

constraintRepairExact : ∀ {Multiplier}
    (pseudoData : FiniteKKTPseudoinverseData Multiplier) vector row →
  constraintApply pseudoData (constraintRepair pseudoData vector) row
  ≡ constraintApply pseudoData vector row
constraintRepairExact pseudoData vector row = trans
  (constraintGramActionExact pseudoData
    (pseudoApply pseudoData (constraintApply pseudoData vector)) row)
  (gramPseudoFixesConstraintImage pseudoData vector row)

projectConstraintZero : ∀ {Multiplier}
    (pseudoData : FiniteKKTPseudoinverseData Multiplier) vector →
  ConstraintKernel pseudoData (admissibleProject pseudoData vector)
projectConstraintZero pseudoData vector = record
  { constraintZero = λ row → trans
      (Rect.applyRectangularSubtract KKT.physicalStateCarrier
        (constraintMatrix pseudoData) vector
        (constraintRepair pseudoData vector) row)
      (trans
        (cong (constraintApply pseudoData vector row -_)
          (constraintRepairExact pseudoData vector row))
        (ℚRing.solve-∀ (constraintApply pseudoData vector row))) }

pseudoOfConstraintKernelZero : ∀ {Multiplier}
    (pseudoData : FiniteKKTPseudoinverseData Multiplier) vector →
  ConstraintKernel pseudoData vector →
  ∀ row → pseudoApply pseudoData (constraintApply pseudoData vector) row ≡ 0ℚ
pseudoOfConstraintKernelZero pseudoData vector kernel row = trans
  (Rect.applyRectangularVectorCong (multiplierCarrier pseudoData)
    (gramPseudoinverse pseudoData) (constraintZero kernel) row)
  (Rect.applyRectangularZero
    (multiplierCarrier pseudoData) (gramPseudoinverse pseudoData) row)

repairOfConstraintKernelZero : ∀ {Multiplier}
    (pseudoData : FiniteKKTPseudoinverseData Multiplier) vector →
  ConstraintKernel pseudoData vector →
  ∀ coordinate → constraintRepair pseudoData vector coordinate ≡ 0ℚ
repairOfConstraintKernelZero pseudoData vector kernel coordinate = trans
  (Rect.applyRectangularVectorCong (multiplierCarrier pseudoData)
    (Rect.transposeRectangular (constraintMatrix pseudoData))
    (pseudoOfConstraintKernelZero pseudoData vector kernel) coordinate)
  (Rect.applyRectangularZero (multiplierCarrier pseudoData)
    (Rect.transposeRectangular (constraintMatrix pseudoData)) coordinate)

projectFixesConstraintKernel : ∀ {Multiplier}
    (pseudoData : FiniteKKTPseudoinverseData Multiplier) vector →
  ConstraintKernel pseudoData vector →
  ∀ coordinate → admissibleProject pseudoData vector coordinate ≡ vector coordinate
projectFixesConstraintKernel pseudoData vector kernel coordinate = trans
  (cong (vector coordinate -_)
    (repairOfConstraintKernelZero pseudoData vector kernel coordinate))
  (ℚRing.solve-∀ (vector coordinate))

projectIdempotent : ∀ {Multiplier}
    (pseudoData : FiniteKKTPseudoinverseData Multiplier) vector coordinate →
  admissibleProject pseudoData (admissibleProject pseudoData vector) coordinate
  ≡ admissibleProject pseudoData vector coordinate
projectIdempotent pseudoData vector = projectFixesConstraintKernel pseudoData
  (admissibleProject pseudoData vector) (projectConstraintZero pseudoData vector)

repairOfAdjointExact : ∀ {Multiplier}
    (pseudoData : FiniteKKTPseudoinverseData Multiplier) multiplier coordinate →
  constraintRepair pseudoData (constraintAdjointApply pseudoData multiplier) coordinate
  ≡ constraintAdjointApply pseudoData multiplier coordinate
repairOfAdjointExact pseudoData multiplier coordinate =
  let constraintToGram = constraintGramActionExact pseudoData multiplier in
  trans
    (Rect.applyRectangularVectorCong (multiplierCarrier pseudoData)
      (Rect.transposeRectangular (constraintMatrix pseudoData))
      (λ row → Rect.applyRectangularVectorCong
        (multiplierCarrier pseudoData) (gramPseudoinverse pseudoData)
        constraintToGram row) coordinate)
    (adjointPseudoGramFixesAdjointImage pseudoData multiplier coordinate)

projectKillsAdjointRange : ∀ {Multiplier}
    (pseudoData : FiniteKKTPseudoinverseData Multiplier) vector →
  AdjointRange pseudoData vector →
  ∀ coordinate → admissibleProject pseudoData vector coordinate ≡ 0ℚ
projectKillsAdjointRange pseudoData vector range coordinate =
  let
    repairRepresentation =
      Rect.applyRectangularVectorCong (multiplierCarrier pseudoData)
        (Rect.transposeRectangular (constraintMatrix pseudoData))
        (λ row → Rect.applyRectangularVectorCong
          (multiplierCarrier pseudoData) (gramPseudoinverse pseudoData)
          (λ selected → Rect.applyRectangularVectorCong
            KKT.physicalStateCarrier (constraintMatrix pseudoData)
            (representedByAdjoint range) selected) row) coordinate
    repairIsVector = trans repairRepresentation
      (trans (repairOfAdjointExact pseudoData (multiplier range) coordinate)
        (sym (representedByAdjoint range coordinate)))
  in trans (cong (vector coordinate -_) repairIsVector)
      (ℚRing.solve-∀ (vector coordinate))

repairSelfAdjoint : ∀ {Multiplier}
    (pseudoData : FiniteKKTPseudoinverseData Multiplier) left right →
  KKT.stateDot left (constraintRepair pseudoData right)
  ≡ KKT.stateDot (constraintRepair pseudoData left) right
repairSelfAdjoint pseudoData left right = trans
  (sym (Rect.rectangularAdjointExact
    (multiplierCarrier pseudoData) KKT.physicalStateCarrier
    (constraintMatrix pseudoData) left
    (pseudoApply pseudoData (constraintApply pseudoData right))))
  (trans
    (Rect.symmetricMatrixMovesAcrossDot
      (multiplierCarrier pseudoData) (gramPseudoinverse pseudoData)
      (gramPseudoinverseSymmetric pseudoData)
      (constraintApply pseudoData left) (constraintApply pseudoData right))
    (trans
      (Rect.finiteDotSymmetric (multiplierCarrier pseudoData)
        (pseudoApply pseudoData (constraintApply pseudoData left))
        (constraintApply pseudoData right))
      (trans
        (Rect.rectangularAdjointExact
          (multiplierCarrier pseudoData) KKT.physicalStateCarrier
          (constraintMatrix pseudoData) right
          (pseudoApply pseudoData (constraintApply pseudoData left)))
        (Rect.finiteDotSymmetric KKT.physicalStateCarrier right
          (constraintRepair pseudoData left)))))

projectSelfAdjoint : ∀ {Multiplier}
    (pseudoData : FiniteKKTPseudoinverseData Multiplier) left right →
  KKT.stateDot left (admissibleProject pseudoData right)
  ≡ KKT.stateDot (admissibleProject pseudoData left) right
projectSelfAdjoint pseudoData left right = trans
  (Rect.finiteDotSubtractRight KKT.physicalStateCarrier
    left right (constraintRepair pseudoData right))
  (trans
    (cong (KKT.stateDot left right -_)
      (repairSelfAdjoint pseudoData left right))
    (sym (Rect.finiteDotSubtractLeft KKT.physicalStateCarrier
      left (constraintRepair pseudoData left) right)))

record ProjectionUniversalProperty {Multiplier : Set}
    (pseudoData : FiniteKKTPseudoinverseData Multiplier)
    (source candidate : KKT.StateVector) : Set₁ where
  field
    candidateAdmissible : ConstraintKernel pseudoData candidate
    defectMultiplier : MultiplierVector Multiplier
    defectInAdjointRange : ∀ coordinate →
      source coordinate - candidate coordinate
      ≡ constraintAdjointApply pseudoData defectMultiplier coordinate
open ProjectionUniversalProperty public

projectSatisfiesUniversalProperty : ∀ {Multiplier}
    (pseudoData : FiniteKKTPseudoinverseData Multiplier) source →
  ProjectionUniversalProperty pseudoData source (admissibleProject pseudoData source)
projectSatisfiesUniversalProperty pseudoData source = record
  { candidateAdmissible = projectConstraintZero pseudoData source
  ; defectMultiplier = pseudoApply pseudoData (constraintApply pseudoData source)
  ; defectInAdjointRange = λ coordinate → ℚRing.solve-∀
      (source coordinate) (constraintRepair pseudoData source coordinate) }

universalPropertyUnique : ∀ {Multiplier}
    (pseudoData : FiniteKKTPseudoinverseData Multiplier) source candidate →
  ProjectionUniversalProperty pseudoData source candidate →
  ∀ coordinate → candidate coordinate ≡ admissibleProject pseudoData source coordinate
universalPropertyUnique pseudoData source candidate property coordinate =
  let
    μ = defectMultiplier property
    sourceAsCandidatePlusAdjoint : ∀ selected →
      source selected ≡ candidate selected
        + constraintAdjointApply pseudoData μ selected
    sourceAsCandidatePlusAdjoint selected = trans
      (sym (ℚRing.solve-∀ (source selected) (candidate selected)
        (constraintAdjointApply pseudoData μ selected)))
      (trans (cong (_+ candidate selected)
        (defectInAdjointRange property selected))
        (ℚRing.solve-∀ (candidate selected)
          (constraintAdjointApply pseudoData μ selected)))
    sourceConstraintIsGram : ∀ row →
      constraintApply pseudoData source row ≡ gramApply pseudoData μ row
    sourceConstraintIsGram row = trans
      (Rect.applyRectangularVectorCong KKT.physicalStateCarrier
        (constraintMatrix pseudoData) sourceAsCandidatePlusAdjoint row)
      (trans
        (Rect.applyRectangularAdd KKT.physicalStateCarrier
          (constraintMatrix pseudoData) candidate
          (constraintAdjointApply pseudoData μ) row)
        (trans (cong₂ _+_
          (constraintZero (candidateAdmissible property) row)
          (constraintGramActionExact pseudoData μ row))
          (ℚRing.solve-∀ (gramApply pseudoData μ row))))
    repairSourceIsAdjoint : ∀ selected →
      constraintRepair pseudoData source selected
      ≡ constraintAdjointApply pseudoData μ selected
    repairSourceIsAdjoint selected = trans
      (Rect.applyRectangularVectorCong (multiplierCarrier pseudoData)
        (Rect.transposeRectangular (constraintMatrix pseudoData))
        (λ row → Rect.applyRectangularVectorCong
          (multiplierCarrier pseudoData) (gramPseudoinverse pseudoData)
          sourceConstraintIsGram row) selected)
      (adjointPseudoGramFixesAdjointImage pseudoData μ selected)
  in sym (trans
    (cong (source coordinate -_) (repairSourceIsAdjoint coordinate))
    (trans (cong (_- constraintAdjointApply pseudoData μ coordinate)
      (sourceAsCandidatePlusAdjoint coordinate))
      (ℚRing.solve-∀ (candidate coordinate)
        (constraintAdjointApply pseudoData μ coordinate))))

fullInverseToPseudoinverse : ∀ {Multiplier} →
  KKT.FiniteKKTProjectorData Multiplier →
  FiniteKKTPseudoinverseData Multiplier
fullInverseToPseudoinverse projectorData = record
  { multiplierCarrier = KKT.multiplierCarrier projectorData
  ; constraintMatrix = KKT.constraintMatrix projectorData
  ; gramPseudoinverse = KKT.multiplierGreen projectorData
  ; gramPseudoinverseSymmetric = KKT.gramInverseSymmetric projectorData
  ; gramPseudoGramAction = λ multiplier row →
      Rect.applyRectangularVectorCong
        (KKT.multiplierCarrier projectorData)
        (KKT.constraintGram projectorData)
        (Matrix.matrixInverseLeftExact
          (KKT.gramInverseCertificate projectorData)
          (Rect.applyRectangular (KKT.multiplierCarrier projectorData)
            (KKT.constraintGram projectorData) multiplier)) row
  ; pseudoGramPseudoAction = λ multiplier row →
      Matrix.matrixInverseLeftExact
        (KKT.gramInverseCertificate projectorData)
        (KKT.multiplierGreenApply projectorData multiplier) row
  ; gramPseudoSymmetric = λ left right → trans
      (Matrix.operatorTimesInverse
        (KKT.gramInverseCertificate projectorData) left right)
      (sym (Matrix.operatorTimesInverse
        (KKT.gramInverseCertificate projectorData) right left))
  ; pseudoGramSymmetric = λ left right → trans
      (Matrix.inverseTimesOperator
        (KKT.gramInverseCertificate projectorData) left right)
      (sym (Matrix.inverseTimesOperator
        (KKT.gramInverseCertificate projectorData) right left))
  ; gramPseudoFixesConstraintImage = λ state row →
      Matrix.matrixInverseRightExact
        (KKT.gramInverseCertificate projectorData)
        (KKT.constraintApply projectorData state) row
  ; adjointPseudoGramFixesAdjointImage = λ multiplier coordinate →
      Rect.applyRectangularVectorCong
        (KKT.multiplierCarrier projectorData)
        (Rect.transposeRectangular (KKT.constraintMatrix projectorData))
        (Matrix.matrixInverseLeftExact
          (KKT.gramInverseCertificate projectorData) multiplier) coordinate }

finiteKKTPseudoinverseProjectorLevel : ProofLevel
finiteKKTPseudoinverseProjectorLevel = machineChecked

finiteKKTPseudoinverseUniversalPropertyLevel : ProofLevel
finiteKKTPseudoinverseUniversalPropertyLevel = machineChecked

selectedPhysicalPseudoinverseProducerLevel : ProofLevel
selectedPhysicalPseudoinverseProducerLevel = conditional
