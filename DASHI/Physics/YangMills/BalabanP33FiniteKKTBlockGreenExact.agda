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
    (data : ConstrainedGreenData Multiplier) →
  (Multiplier → ℚ) → KKT.StateVector
liftConstraintSource data source =
  KKT.constraintAdjointApply (projectorData data)
    (KKT.multiplierGreenApply (projectorData data) source)

liftConstraintSourceExact : ∀ {Multiplier}
    (data : ConstrainedGreenData Multiplier) source row →
  KKT.constraintApply (projectorData data)
    (liftConstraintSource data source) row ≡ source row
liftConstraintSourceExact data source row = trans
  (KKT.constraintGramActionExact (projectorData data)
    (KKT.multiplierGreenApply (projectorData data) source) row)
  (Matrix.matrixInverseRightExact
    (KKT.gramInverseCertificate (projectorData data)) source row)

liftConstraintSourceProjectZero : ∀ {Multiplier}
    (data : ConstrainedGreenData Multiplier) source coordinate →
  project data (liftConstraintSource data source) coordinate ≡ 0ℚ
liftConstraintSourceProjectZero data source coordinate =
  KKT.killedByProjector
    (KKT.selectedProjectorKillsRepairSpace
      (projectorData data) (liftConstraintSource data source)
      record
        { KKT.SelectedRepairSpace.multiplier =
            KKT.multiplierGreenApply (projectorData data) source
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
blockStateSolution data stateSource multiplierSource =
  let
    lifted = liftConstraintSource data multiplierSource
    reducedSource = Rect.vectorSubtract stateSource (hessianApply data lifted)
  in Rect.vectorAdd (green data reducedSource) lifted

blockResidual : ∀ {Multiplier} →
  ConstrainedGreenData Multiplier → KKT.StateVector →
  (Multiplier → ℚ) → KKT.StateVector
blockResidual data stateSource multiplierSource =
  Rect.vectorSubtract stateSource
    (hessianApply data (blockStateSolution data stateSource multiplierSource))

blockMultiplierSolution : ∀ {Multiplier} →
  ConstrainedGreenData Multiplier → KKT.StateVector →
  (Multiplier → ℚ) → Multiplier → ℚ
blockMultiplierSolution data stateSource multiplierSource =
  KKT.multiplierGreenApply (projectorData data)
    (KKT.constraintApply (projectorData data)
      (blockResidual data stateSource multiplierSource))

solveKKTBlock : ∀ {Multiplier} → ConstrainedGreenData Multiplier →
  KKTBlockVector Multiplier → KKTBlockVector Multiplier
solveKKTBlock data source = block
  (blockStateSolution data (statePart source) (multiplierPart source))
  (blockMultiplierSolution data (statePart source) (multiplierPart source))

applyKKTBlock : ∀ {Multiplier} → ConstrainedGreenData Multiplier →
  KKTBlockVector Multiplier → KKTBlockVector Multiplier
applyKKTBlock data vector = block
  (Rect.vectorAdd
    (hessianApply data (statePart vector))
    (KKT.constraintAdjointApply (projectorData data)
      (multiplierPart vector)))
  (KKT.constraintApply (projectorData data) (statePart vector))

blockStateConstraintExact : ∀ {Multiplier}
    (data : ConstrainedGreenData Multiplier)
    stateSource multiplierSource row →
  KKT.constraintApply (projectorData data)
    (blockStateSolution data stateSource multiplierSource) row
  ≡ multiplierSource row
blockStateConstraintExact data stateSource multiplierSource row =
  let
    lifted = liftConstraintSource data multiplierSource
    reducedSource = Rect.vectorSubtract stateSource (hessianApply data lifted)
    z = green data reducedSource
    zKernel : KKT.SelectedConstraintKernel (projectorData data) z
    zKernel = KKT.selectedProjectorImageIsConstraintKernel
      (projectorData data) z
      record { KKT.SelectedProjectorImage.fixedByProjector =
        greenProjectFixed data reducedSource }
  in trans (constraintAddExact data z lifted row)
    (trans
      (cong₂ _+_ (KKT.constraintZero zKernel row)
        (liftConstraintSourceExact data multiplierSource row))
      (ℚRing.solve-∀ (multiplierSource row)))

projectedBlockResidualZero : ∀ {Multiplier}
    (data : ConstrainedGreenData Multiplier)
    stateSource multiplierSource coordinate →
  project data (blockResidual data stateSource multiplierSource) coordinate
  ≡ 0ℚ
projectedBlockResidualZero data stateSource multiplierSource coordinate =
  let
    lifted = liftConstraintSource data multiplierSource
    reducedSource = Rect.vectorSubtract stateSource (hessianApply data lifted)
    z = green data reducedSource
    state = Rect.vectorAdd z lifted
    projectZ : ∀ selected → project data z selected ≡ z selected
    projectZ = greenProjectFixed data reducedSource
    hessianStateSplit : ∀ selected →
      hessianApply data state selected
      ≡ hessianApply data z selected + hessianApply data lifted selected
    hessianStateSplit = hessianAddExact data z lifted
    residualAsReducedMinusHz : ∀ selected →
      blockResidual data stateSource multiplierSource selected
      ≡ Rect.vectorSubtract reducedSource (hessianApply data z) selected
    residualAsReducedMinusHz selected = trans
      (cong (stateSource selected -_) (hessianStateSplit selected))
      (ℚRing.solve-∀ (stateSource selected)
        (hessianApply data lifted selected) (hessianApply data z selected))
    projectedHzIsProjectedReduced : ∀ selected →
      project data (hessianApply data z) selected
      ≡ project data reducedSource selected
    projectedHzIsProjectedReduced selected =
      let
        projectedHessian = projectedHessianAfterGreen data reducedSource selected
        replaceInnerProject :
          project data (hessianApply data (project data z)) selected
          ≡ project data (hessianApply data z) selected
        replaceInnerProject = projectPointwiseCong data
          (hessianPointwiseCong data projectZ) selected
      in trans (sym replaceInnerProject) projectedHessian
  in trans (projectPointwiseCong data residualAsReducedMinusHz coordinate)
    (trans (projectSubtractExact data reducedSource (hessianApply data z) coordinate)
      (trans
        (cong (project data reducedSource coordinate -_)
          (projectedHzIsProjectedReduced coordinate))
        (ℚRing.solve-∀ (project data reducedSource coordinate))))

blockResidualIsRepair : ∀ {Multiplier}
    (data : ConstrainedGreenData Multiplier)
    stateSource multiplierSource coordinate →
  blockResidual data stateSource multiplierSource coordinate
  ≡ KKT.selectedConstraintRepair (projectorData data)
      (blockResidual data stateSource multiplierSource) coordinate
blockResidualIsRepair data stateSource multiplierSource coordinate =
  let
    residual = blockResidual data stateSource multiplierSource
    decomposition = KKT.selectedAdmissibleOrthogonalDecompositionPointwise
      (projectorData data) residual coordinate
    projectedZero = projectedBlockResidualZero
      data stateSource multiplierSource coordinate
  in trans decomposition
    (trans
      (cong (_+ KKT.selectedConstraintRepair
        (projectorData data) residual coordinate) projectedZero)
      (ℚRing.solve-∀
        (KKT.selectedConstraintRepair (projectorData data) residual coordinate)))

blockStateEquationExact : ∀ {Multiplier}
    (data : ConstrainedGreenData Multiplier)
    stateSource multiplierSource coordinate →
  Rect.vectorAdd
    (hessianApply data (blockStateSolution data stateSource multiplierSource))
    (KKT.constraintAdjointApply (projectorData data)
      (blockMultiplierSolution data stateSource multiplierSource))
    coordinate ≡ stateSource coordinate
blockStateEquationExact data stateSource multiplierSource coordinate =
  let
    state = blockStateSolution data stateSource multiplierSource
    residual = blockResidual data stateSource multiplierSource
    adjointMultiplierIsRepair :
      KKT.constraintAdjointApply (projectorData data)
        (blockMultiplierSolution data stateSource multiplierSource) coordinate
      ≡ KKT.selectedConstraintRepair (projectorData data) residual coordinate
    adjointMultiplierIsRepair = refl
  in trans
    (cong (hessianApply data state coordinate +_) adjointMultiplierIsRepair)
    (trans
      (cong (hessianApply data state coordinate +_)
        (sym (blockResidualIsRepair data stateSource multiplierSource coordinate)))
      (ℚRing.solve-∀ (stateSource coordinate)
        (hessianApply data state coordinate)))

record PointwiseKKTBlockEquality {Multiplier : Set}
    (left right : KKTBlockVector Multiplier) : Set where
  field
    stateEqual : ∀ coordinate → statePart left coordinate ≡ statePart right coordinate
    multiplierEqual : ∀ row → multiplierPart left row ≡ multiplierPart right row
open PointwiseKKTBlockEquality public

kktBlockRightInverseExact : ∀ {Multiplier}
    (data : ConstrainedGreenData Multiplier) source →
  PointwiseKKTBlockEquality
    (applyKKTBlock data (solveKKTBlock data source)) source
kktBlockRightInverseExact data source = record
  { stateEqual = blockStateEquationExact data
      (statePart source) (multiplierPart source)
  ; multiplierEqual = blockStateConstraintExact data
      (statePart source) (multiplierPart source) }

finiteKKTBlockSolveLevel : ProofLevel
finiteKKTBlockSolveLevel = machineChecked

finiteBrezziRightInverseLevel : ProofLevel
finiteBrezziRightInverseLevel = machineChecked

finiteKKTBlockTwoSidedInverseProducerLevel : ProofLevel
finiteKKTBlockTwoSidedInverseProducerLevel = conditional
