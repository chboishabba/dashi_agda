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
constraintApply data = Rect.applyRectangular
  KKT.physicalStateCarrier (constraintMatrix data)

constraintAdjointApply : ∀ {Multiplier} →
  FiniteKKTPseudoinverseData Multiplier →
  MultiplierVector Multiplier → KKT.StateVector
constraintAdjointApply data = Rect.applyRectangular
  (multiplierCarrier data)
  (Rect.transposeRectangular (constraintMatrix data))

constraintGram : ∀ {Multiplier} →
  FiniteKKTPseudoinverseData Multiplier → Matrix.RationalMatrix Multiplier
constraintGram data = constraintGramRaw
  (multiplierCarrier data) (constraintMatrix data)

gramApply : ∀ {Multiplier} →
  FiniteKKTPseudoinverseData Multiplier →
  MultiplierVector Multiplier → MultiplierVector Multiplier
gramApply data = Rect.applyRectangular
  (multiplierCarrier data) (constraintGram data)

pseudoApply : ∀ {Multiplier} →
  FiniteKKTPseudoinverseData Multiplier →
  MultiplierVector Multiplier → MultiplierVector Multiplier
pseudoApply data = Rect.applyRectangular
  (multiplierCarrier data) (gramPseudoinverse data)

constraintRepair : ∀ {Multiplier} →
  FiniteKKTPseudoinverseData Multiplier →
  KKT.StateVector → KKT.StateVector
constraintRepair data vector = constraintAdjointApply data
  (pseudoApply data (constraintApply data vector))

admissibleProject : ∀ {Multiplier} →
  FiniteKKTPseudoinverseData Multiplier →
  KKT.StateVector → KKT.StateVector
admissibleProject data vector =
  Rect.vectorSubtract vector (constraintRepair data vector)

record ConstraintKernel {Multiplier : Set}
    (data : FiniteKKTPseudoinverseData Multiplier)
    (vector : KKT.StateVector) : Set where
  field
    constraintZero : ∀ row → constraintApply data vector row ≡ 0ℚ
open ConstraintKernel public

record AdjointRange {Multiplier : Set}
    (data : FiniteKKTPseudoinverseData Multiplier)
    (vector : KKT.StateVector) : Set₁ where
  field
    multiplier : MultiplierVector Multiplier
    representedByAdjoint : ∀ coordinate →
      vector coordinate ≡ constraintAdjointApply data multiplier coordinate
open AdjointRange public

constraintGramActionExact : ∀ {Multiplier}
    (data : FiniteKKTPseudoinverseData Multiplier) multiplier row →
  constraintApply data (constraintAdjointApply data multiplier) row
  ≡ gramApply data multiplier row
constraintGramActionExact data multiplier row = sym
  (Rect.applyComposeRectangularExact
    KKT.physicalStateCarrier (multiplierCarrier data)
    (constraintMatrix data)
    (Rect.transposeRectangular (constraintMatrix data))
    multiplier row)

constraintRepairExact : ∀ {Multiplier}
    (data : FiniteKKTPseudoinverseData Multiplier) vector row →
  constraintApply data (constraintRepair data vector) row
  ≡ constraintApply data vector row
constraintRepairExact data vector row = trans
  (constraintGramActionExact data
    (pseudoApply data (constraintApply data vector)) row)
  (gramPseudoFixesConstraintImage data vector row)

projectConstraintZero : ∀ {Multiplier}
    (data : FiniteKKTPseudoinverseData Multiplier) vector →
  ConstraintKernel data (admissibleProject data vector)
projectConstraintZero data vector = record
  { constraintZero = λ row → trans
      (Rect.applyRectangularSubtract KKT.physicalStateCarrier
        (constraintMatrix data) vector (constraintRepair data vector) row)
      (trans
        (cong (constraintApply data vector row -_)
          (constraintRepairExact data vector row))
        (ℚRing.solve-∀ (constraintApply data vector row))) }

pseudoOfConstraintKernelZero : ∀ {Multiplier}
    (data : FiniteKKTPseudoinverseData Multiplier) vector →
  ConstraintKernel data vector →
  ∀ row → pseudoApply data (constraintApply data vector) row ≡ 0ℚ
pseudoOfConstraintKernelZero data vector kernel row = trans
  (Rect.applyRectangularVectorCong (multiplierCarrier data)
    (gramPseudoinverse data) (constraintZero kernel) row)
  (Rect.applyRectangularZero
    (multiplierCarrier data) (gramPseudoinverse data) row)

repairOfConstraintKernelZero : ∀ {Multiplier}
    (data : FiniteKKTPseudoinverseData Multiplier) vector →
  ConstraintKernel data vector →
  ∀ coordinate → constraintRepair data vector coordinate ≡ 0ℚ
repairOfConstraintKernelZero data vector kernel coordinate = trans
  (Rect.applyRectangularVectorCong (multiplierCarrier data)
    (Rect.transposeRectangular (constraintMatrix data))
    (pseudoOfConstraintKernelZero data vector kernel) coordinate)
  (Rect.applyRectangularZero (multiplierCarrier data)
    (Rect.transposeRectangular (constraintMatrix data)) coordinate)

projectFixesConstraintKernel : ∀ {Multiplier}
    (data : FiniteKKTPseudoinverseData Multiplier) vector →
  ConstraintKernel data vector →
  ∀ coordinate → admissibleProject data vector coordinate ≡ vector coordinate
projectFixesConstraintKernel data vector kernel coordinate = trans
  (cong (vector coordinate -_)
    (repairOfConstraintKernelZero data vector kernel coordinate))
  (ℚRing.solve-∀ (vector coordinate))

projectIdempotent : ∀ {Multiplier}
    (data : FiniteKKTPseudoinverseData Multiplier) vector coordinate →
  admissibleProject data (admissibleProject data vector) coordinate
  ≡ admissibleProject data vector coordinate
projectIdempotent data vector = projectFixesConstraintKernel data
  (admissibleProject data vector) (projectConstraintZero data vector)

repairOfAdjointExact : ∀ {Multiplier}
    (data : FiniteKKTPseudoinverseData Multiplier) multiplier coordinate →
  constraintRepair data (constraintAdjointApply data multiplier) coordinate
  ≡ constraintAdjointApply data multiplier coordinate
repairOfAdjointExact data multiplier coordinate =
  let constraintToGram = constraintGramActionExact data multiplier in
  trans
    (Rect.applyRectangularVectorCong (multiplierCarrier data)
      (Rect.transposeRectangular (constraintMatrix data))
      (λ row → Rect.applyRectangularVectorCong
        (multiplierCarrier data) (gramPseudoinverse data)
        constraintToGram row) coordinate)
    (adjointPseudoGramFixesAdjointImage data multiplier coordinate)

projectKillsAdjointRange : ∀ {Multiplier}
    (data : FiniteKKTPseudoinverseData Multiplier) vector →
  AdjointRange data vector →
  ∀ coordinate → admissibleProject data vector coordinate ≡ 0ℚ
projectKillsAdjointRange data vector range coordinate =
  let
    repairRepresentation =
      Rect.applyRectangularVectorCong (multiplierCarrier data)
        (Rect.transposeRectangular (constraintMatrix data))
        (λ row → Rect.applyRectangularVectorCong
          (multiplierCarrier data) (gramPseudoinverse data)
          (λ selected → Rect.applyRectangularVectorCong
            KKT.physicalStateCarrier (constraintMatrix data)
            (representedByAdjoint range) selected) row) coordinate
    repairIsVector = trans repairRepresentation
      (trans (repairOfAdjointExact data (multiplier range) coordinate)
        (sym (representedByAdjoint range coordinate)))
  in trans (cong (vector coordinate -_) repairIsVector)
      (ℚRing.solve-∀ (vector coordinate))

repairSelfAdjoint : ∀ {Multiplier}
    (data : FiniteKKTPseudoinverseData Multiplier) left right →
  KKT.stateDot left (constraintRepair data right)
  ≡ KKT.stateDot (constraintRepair data left) right
repairSelfAdjoint data left right = trans
  (sym (Rect.rectangularAdjointExact
    (multiplierCarrier data) KKT.physicalStateCarrier
    (constraintMatrix data) left
    (pseudoApply data (constraintApply data right))))
  (trans
    (Rect.symmetricMatrixMovesAcrossDot
      (multiplierCarrier data) (gramPseudoinverse data)
      (gramPseudoinverseSymmetric data)
      (constraintApply data left) (constraintApply data right))
    (trans
      (Rect.finiteDotSymmetric (multiplierCarrier data)
        (pseudoApply data (constraintApply data left))
        (constraintApply data right))
      (trans
        (Rect.rectangularAdjointExact
          (multiplierCarrier data) KKT.physicalStateCarrier
          (constraintMatrix data) right
          (pseudoApply data (constraintApply data left)))
        (Rect.finiteDotSymmetric KKT.physicalStateCarrier right
          (constraintRepair data left)))))

projectSelfAdjoint : ∀ {Multiplier}
    (data : FiniteKKTPseudoinverseData Multiplier) left right →
  KKT.stateDot left (admissibleProject data right)
  ≡ KKT.stateDot (admissibleProject data left) right
projectSelfAdjoint data left right = trans
  (Rect.finiteDotSubtractRight KKT.physicalStateCarrier
    left right (constraintRepair data right))
  (trans
    (cong (KKT.stateDot left right -_)
      (repairSelfAdjoint data left right))
    (sym (Rect.finiteDotSubtractLeft KKT.physicalStateCarrier
      left (constraintRepair data left) right)))

record ProjectionUniversalProperty {Multiplier : Set}
    (data : FiniteKKTPseudoinverseData Multiplier)
    (source candidate : KKT.StateVector) : Set₁ where
  field
    candidateAdmissible : ConstraintKernel data candidate
    defectMultiplier : MultiplierVector Multiplier
    defectInAdjointRange : ∀ coordinate →
      source coordinate - candidate coordinate
      ≡ constraintAdjointApply data defectMultiplier coordinate
open ProjectionUniversalProperty public

projectSatisfiesUniversalProperty : ∀ {Multiplier}
    (data : FiniteKKTPseudoinverseData Multiplier) source →
  ProjectionUniversalProperty data source (admissibleProject data source)
projectSatisfiesUniversalProperty data source = record
  { candidateAdmissible = projectConstraintZero data source
  ; defectMultiplier = pseudoApply data (constraintApply data source)
  ; defectInAdjointRange = λ coordinate → ℚRing.solve-∀
      (source coordinate) (constraintRepair data source coordinate) }

universalPropertyUnique : ∀ {Multiplier}
    (data : FiniteKKTPseudoinverseData Multiplier) source candidate →
  ProjectionUniversalProperty data source candidate →
  ∀ coordinate → candidate coordinate ≡ admissibleProject data source coordinate
universalPropertyUnique data source candidate property coordinate =
  let
    μ = defectMultiplier property
    sourceAsCandidatePlusAdjoint : ∀ selected →
      source selected ≡ candidate selected + constraintAdjointApply data μ selected
    sourceAsCandidatePlusAdjoint selected = trans
      (sym (ℚRing.solve-∀ (source selected) (candidate selected)
        (constraintAdjointApply data μ selected)))
      (trans (cong (_+ candidate selected)
        (defectInAdjointRange property selected))
        (ℚRing.solve-∀ (candidate selected)
          (constraintAdjointApply data μ selected)))
    sourceConstraintIsGram : ∀ row →
      constraintApply data source row ≡ gramApply data μ row
    sourceConstraintIsGram row = trans
      (Rect.applyRectangularVectorCong KKT.physicalStateCarrier
        (constraintMatrix data) sourceAsCandidatePlusAdjoint row)
      (trans
        (Rect.applyRectangularAdd KKT.physicalStateCarrier
          (constraintMatrix data) candidate
          (constraintAdjointApply data μ) row)
        (trans (cong₂ _+_
          (constraintZero (candidateAdmissible property) row)
          (constraintGramActionExact data μ row))
          (ℚRing.solve-∀ (gramApply data μ row))))
    repairSourceIsAdjoint : ∀ selected →
      constraintRepair data source selected
      ≡ constraintAdjointApply data μ selected
    repairSourceIsAdjoint selected = trans
      (Rect.applyRectangularVectorCong (multiplierCarrier data)
        (Rect.transposeRectangular (constraintMatrix data))
        (λ row → Rect.applyRectangularVectorCong
          (multiplierCarrier data) (gramPseudoinverse data)
          sourceConstraintIsGram row) selected)
      (adjointPseudoGramFixesAdjointImage data μ selected)
  in sym (trans
    (cong (source coordinate -_) (repairSourceIsAdjoint coordinate))
    (trans (cong (_- constraintAdjointApply data μ coordinate)
      (sourceAsCandidatePlusAdjoint coordinate))
      (ℚRing.solve-∀ (candidate coordinate)
        (constraintAdjointApply data μ coordinate))))

fullInverseToPseudoinverse : ∀ {Multiplier} →
  KKT.FiniteKKTProjectorData Multiplier →
  FiniteKKTPseudoinverseData Multiplier
fullInverseToPseudoinverse data = record
  { multiplierCarrier = KKT.multiplierCarrier data
  ; constraintMatrix = KKT.constraintMatrix data
  ; gramPseudoinverse = KKT.multiplierGreen data
  ; gramPseudoinverseSymmetric = KKT.gramInverseSymmetric data
  ; gramPseudoGramAction = λ multiplier row →
      Rect.applyRectangularVectorCong
        (KKT.multiplierCarrier data) (KKT.constraintGram data)
        (Matrix.matrixInverseLeftExact
          (KKT.gramInverseCertificate data)
          (Rect.applyRectangular (KKT.multiplierCarrier data)
            (KKT.constraintGram data) multiplier)) row
  ; pseudoGramPseudoAction = λ multiplier row →
      Matrix.matrixInverseLeftExact
        (KKT.gramInverseCertificate data)
        (KKT.multiplierGreenApply data multiplier) row
  ; gramPseudoSymmetric = λ left right → trans
      (Matrix.operatorTimesInverse
        (KKT.gramInverseCertificate data) left right)
      (sym (Matrix.operatorTimesInverse
        (KKT.gramInverseCertificate data) right left))
  ; pseudoGramSymmetric = λ left right → trans
      (Matrix.inverseTimesOperator
        (KKT.gramInverseCertificate data) left right)
      (sym (Matrix.inverseTimesOperator
        (KKT.gramInverseCertificate data) right left))
  ; gramPseudoFixesConstraintImage = λ state row →
      Matrix.matrixInverseRightExact
        (KKT.gramInverseCertificate data)
        (KKT.constraintApply data state) row
  ; adjointPseudoGramFixesAdjointImage = λ multiplier coordinate →
      Rect.applyRectangularVectorCong
        (KKT.multiplierCarrier data)
        (Rect.transposeRectangular (KKT.constraintMatrix data))
        (Matrix.matrixInverseLeftExact
          (KKT.gramInverseCertificate data) multiplier) coordinate }

finiteKKTPseudoinverseProjectorLevel : ProofLevel
finiteKKTPseudoinverseProjectorLevel = machineChecked

finiteKKTPseudoinverseUniversalPropertyLevel : ProofLevel
finiteKKTPseudoinverseUniversalPropertyLevel = machineChecked

selectedPhysicalPseudoinverseProducerLevel : ProofLevel
selectedPhysicalPseudoinverseProducerLevel = conditional
