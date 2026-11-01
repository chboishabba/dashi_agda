module DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockGreenExact where

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
-- Solve the finite local saddle/KKT system from the multiplier Gram inverse
-- and a Green operator for P H P on ker L. The exact formula proves
--
--   H v + L* mu = f,     L v = g
--
-- pointwise, without asking for an ambient inverse of the singular P H P.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
open import DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockGreenAlgebraExact public

liftConstraintSource : ∀ {Multiplier}
    (greenData : ConstrainedGreenData Multiplier) →
  (Multiplier → ℚ) → KKT.StateVector
liftConstraintSource greenData source =
  KKT.constraintAdjointApply (projectorData greenData)
    (KKT.multiplierGreenApply (projectorData greenData) source)

liftConstraintSourceExact : ∀ {Multiplier}
    (greenData : ConstrainedGreenData Multiplier) source row →
  KKT.constraintApply (projectorData greenData)
    (liftConstraintSource greenData source) row ≡ source row
liftConstraintSourceExact greenData source row = trans
  (KKT.constraintGramActionExact (projectorData greenData)
    (KKT.multiplierGreenApply (projectorData greenData) source) row)
  (Matrix.matrixInverseRightExact
    (KKT.gramInverseCertificate (projectorData greenData)) source row)

liftConstraintSourceProjectZero : ∀ {Multiplier}
    (greenData : ConstrainedGreenData Multiplier) source coordinate →
  project greenData (liftConstraintSource greenData source) coordinate ≡ 0ℚ
liftConstraintSourceProjectZero greenData source coordinate =
  KKT.killedByProjector
    (KKT.selectedProjectorKillsRepairSpace
      (projectorData greenData) (liftConstraintSource greenData source)
      record
        { KKT.SelectedRepairSpace.multiplier =
            KKT.multiplierGreenApply (projectorData greenData) source
        ; KKT.SelectedRepairSpace.representedByAdjoint = λ selected → refl })
    coordinate

record KKTBlockVector (Multiplier : Set) : Set where
  constructor block
  field
    statePart : KKT.StateVector
    multiplierPart : Multiplier → ℚ
open KKTBlockVector public

blockStateSolution : ∀ {Multiplier} →
  ConstrainedGreenData Multiplier → KKT.StateVector →
  (Multiplier → ℚ) → KKT.StateVector
blockStateSolution greenData stateSource multiplierSource =
  let
    lifted = liftConstraintSource greenData multiplierSource
    reducedSource =
      Rect.vectorSubtract stateSource (hessianApply greenData lifted)
  in Rect.vectorAdd (green greenData reducedSource) lifted

blockResidual : ∀ {Multiplier} →
  ConstrainedGreenData Multiplier → KKT.StateVector →
  (Multiplier → ℚ) → KKT.StateVector
blockResidual greenData stateSource multiplierSource =
  Rect.vectorSubtract stateSource
    (hessianApply greenData
      (blockStateSolution greenData stateSource multiplierSource))

blockMultiplierSolution : ∀ {Multiplier} →
  ConstrainedGreenData Multiplier → KKT.StateVector →
  (Multiplier → ℚ) → Multiplier → ℚ
blockMultiplierSolution greenData stateSource multiplierSource =
  KKT.multiplierGreenApply (projectorData greenData)
    (KKT.constraintApply (projectorData greenData)
      (blockResidual greenData stateSource multiplierSource))

solveKKTBlock : ∀ {Multiplier} → ConstrainedGreenData Multiplier →
  KKTBlockVector Multiplier → KKTBlockVector Multiplier
solveKKTBlock greenData source = block
  (blockStateSolution greenData (statePart source) (multiplierPart source))
  (blockMultiplierSolution greenData (statePart source) (multiplierPart source))

applyKKTBlock : ∀ {Multiplier} → ConstrainedGreenData Multiplier →
  KKTBlockVector Multiplier → KKTBlockVector Multiplier
applyKKTBlock greenData vector = block
  (Rect.vectorAdd
    (hessianApply greenData (statePart vector))
    (KKT.constraintAdjointApply (projectorData greenData)
      (multiplierPart vector)))
  (KKT.constraintApply (projectorData greenData) (statePart vector))

blockStateConstraintExact : ∀ {Multiplier}
    (greenData : ConstrainedGreenData Multiplier)
    stateSource multiplierSource row →
  KKT.constraintApply (projectorData greenData)
    (blockStateSolution greenData stateSource multiplierSource) row
  ≡ multiplierSource row
blockStateConstraintExact greenData stateSource multiplierSource row =
  let
    lifted = liftConstraintSource greenData multiplierSource
    reducedSource =
      Rect.vectorSubtract stateSource (hessianApply greenData lifted)
    z = green greenData reducedSource
    zKernel : KKT.SelectedConstraintKernel (projectorData greenData) z
    zKernel = KKT.selectedProjectorImageIsConstraintKernel
      (projectorData greenData) z
      record { KKT.SelectedProjectorImage.fixedByProjector =
        greenProjectFixed greenData reducedSource }
  in trans (constraintAddExact greenData z lifted row)
    (trans
      (cong₂ _+_ (KKT.constraintZero zKernel row)
        (liftConstraintSourceExact greenData multiplierSource row))
      (ℚRing.solve-∀ (multiplierSource row)))

projectedBlockResidualZero : ∀ {Multiplier}
    (greenData : ConstrainedGreenData Multiplier)
    stateSource multiplierSource coordinate →
  project greenData
    (blockResidual greenData stateSource multiplierSource) coordinate
  ≡ 0ℚ
projectedBlockResidualZero greenData stateSource multiplierSource coordinate =
  let
    lifted = liftConstraintSource greenData multiplierSource
    reducedSource =
      Rect.vectorSubtract stateSource (hessianApply greenData lifted)
    z = green greenData reducedSource
    state = Rect.vectorAdd z lifted
    projectZ : ∀ selected → project greenData z selected ≡ z selected
    projectZ = greenProjectFixed greenData reducedSource
    hessianStateSplit : ∀ selected →
      hessianApply greenData state selected
      ≡ hessianApply greenData z selected
        + hessianApply greenData lifted selected
    hessianStateSplit = hessianAddExact greenData z lifted
    residualAsReducedMinusHz : ∀ selected →
      blockResidual greenData stateSource multiplierSource selected
      ≡ Rect.vectorSubtract reducedSource (hessianApply greenData z) selected
    residualAsReducedMinusHz selected = trans
      (cong (stateSource selected -_) (hessianStateSplit selected))
      (ℚRing.solve-∀ (stateSource selected)
        (hessianApply greenData lifted selected)
        (hessianApply greenData z selected))
    projectedHzIsProjectedReduced : ∀ selected →
      project greenData (hessianApply greenData z) selected
      ≡ project greenData reducedSource selected
    projectedHzIsProjectedReduced selected =
      let
        projectedHessian =
          projectedHessianAfterGreen greenData reducedSource selected
        replaceInnerProject :
          project greenData
            (hessianApply greenData (project greenData z)) selected
          ≡ project greenData (hessianApply greenData z) selected
        replaceInnerProject = projectPointwiseCong greenData
          (hessianPointwiseCong greenData projectZ) selected
      in trans (sym replaceInnerProject) projectedHessian
  in trans
    (projectPointwiseCong greenData residualAsReducedMinusHz coordinate)
    (trans
      (projectSubtractExact greenData reducedSource
        (hessianApply greenData z) coordinate)
      (trans
        (cong (project greenData reducedSource coordinate -_)
          (projectedHzIsProjectedReduced coordinate))
        (ℚRing.solve-∀ (project greenData reducedSource coordinate))))

blockResidualIsRepair : ∀ {Multiplier}
    (greenData : ConstrainedGreenData Multiplier)
    stateSource multiplierSource coordinate →
  blockResidual greenData stateSource multiplierSource coordinate
  ≡ KKT.selectedConstraintRepair (projectorData greenData)
      (blockResidual greenData stateSource multiplierSource) coordinate
blockResidualIsRepair greenData stateSource multiplierSource coordinate =
  let
    residual = blockResidual greenData stateSource multiplierSource
    decomposition = KKT.selectedAdmissibleOrthogonalDecompositionPointwise
      (projectorData greenData) residual coordinate
    projectedZero = projectedBlockResidualZero
      greenData stateSource multiplierSource coordinate
  in trans decomposition
    (trans
      (cong (_+ KKT.selectedConstraintRepair
        (projectorData greenData) residual coordinate) projectedZero)
      (ℚRing.solve-∀
        (KKT.selectedConstraintRepair
          (projectorData greenData) residual coordinate)))

blockStateEquationExact : ∀ {Multiplier}
    (greenData : ConstrainedGreenData Multiplier)
    stateSource multiplierSource coordinate →
  Rect.vectorAdd
    (hessianApply greenData
      (blockStateSolution greenData stateSource multiplierSource))
    (KKT.constraintAdjointApply (projectorData greenData)
      (blockMultiplierSolution greenData stateSource multiplierSource))
    coordinate ≡ stateSource coordinate
blockStateEquationExact greenData stateSource multiplierSource coordinate =
  let
    state = blockStateSolution greenData stateSource multiplierSource
    residual = blockResidual greenData stateSource multiplierSource
    adjointMultiplierIsRepair :
      KKT.constraintAdjointApply (projectorData greenData)
        (blockMultiplierSolution greenData stateSource multiplierSource) coordinate
      ≡ KKT.selectedConstraintRepair (projectorData greenData) residual coordinate
    adjointMultiplierIsRepair = refl
  in trans
    (cong (hessianApply greenData state coordinate +_)
      adjointMultiplierIsRepair)
    (trans
      (cong (hessianApply greenData state coordinate +_)
        (sym (blockResidualIsRepair
          greenData stateSource multiplierSource coordinate)))
      (ℚRing.solve-∀ (stateSource coordinate)
        (hessianApply greenData state coordinate)))

record PointwiseKKTBlockEquality {Multiplier : Set}
    (left right : KKTBlockVector Multiplier) : Set where
  field
    stateEqual : ∀ coordinate →
      statePart left coordinate ≡ statePart right coordinate
    multiplierEqual : ∀ row →
      multiplierPart left row ≡ multiplierPart right row
open PointwiseKKTBlockEquality public

kktBlockRightInverseExact : ∀ {Multiplier}
    (greenData : ConstrainedGreenData Multiplier) source →
  PointwiseKKTBlockEquality
    (applyKKTBlock greenData (solveKKTBlock greenData source)) source
kktBlockRightInverseExact greenData source = record
  { stateEqual = blockStateEquationExact greenData
      (statePart source) (multiplierPart source)
  ; multiplierEqual = blockStateConstraintExact greenData
      (statePart source) (multiplierPart source) }

finiteKKTBlockSolveLevel : ProofLevel
finiteKKTBlockSolveLevel = machineChecked

finiteBrezziRightInverseLevel : ProofLevel
finiteBrezziRightInverseLevel = machineChecked

finiteKKTBlockTwoSidedInverseProducerLevel : ProofLevel
finiteKKTBlockTwoSidedInverseProducerLevel = conditional
