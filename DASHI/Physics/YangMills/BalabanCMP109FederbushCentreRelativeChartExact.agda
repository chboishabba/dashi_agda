module DASHI.Physics.YangMills.BalabanCMP109FederbushCentreRelativeChartExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Close the purely geometric part of the final G1 centre seam.  If a literal
-- contour value U_j and the Federbush centre V are both within the already
-- certified length-24 defect radius 3/256 of one common reference R, then
--
--   || U_j V^-1 - I ||_op <= 3/256 + 3/256 = 3/128 < 1/24.
--
-- CMP98 equation (25) then gives the equation-(38) source chart
--
--   || log(U_j V^-1) ||_op <= 1/12.
--
-- Thus the remaining centre producer is now only the invariant-ball statement
-- that the actual Federbush average V stays within the SAME 3/256 ball as the
-- input contours.  No separate arbitrary estimate on V is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact as Chart
import DASHI.Physics.YangMills.BalabanCMP98Equation38PrincipalLogQuadraticExact as Eq38

record UnitaryDefectGroup (Unitary : Set) : Set₁ where
  field
    kernel : Telescope.UnitaryOperatorDefectKernel Unitary
    inverse : Unitary → Unitary

    associative : ∀ a b c →
      Telescope.multiply kernel (Telescope.multiply kernel a b) c
      ≡ Telescope.multiply kernel a (Telescope.multiply kernel b c)
    identityLeft : ∀ a →
      Telescope.multiply kernel (Telescope.identity kernel) a ≡ a
    identityRight : ∀ a →
      Telescope.multiply kernel a (Telescope.identity kernel) ≡ a
    inverseLeft : ∀ a →
      Telescope.multiply kernel (inverse a) a ≡ Telescope.identity kernel
    inverseRight : ∀ a →
      Telescope.multiply kernel a (inverse a) ≡ Telescope.identity kernel

open UnitaryDefectGroup public

relative : ∀ {Unitary} → UnitaryDefectGroup Unitary → Unitary → Unitary → Unitary
relative group left right =
  Telescope.multiply (kernel group) left (inverse group right)

relativeFactorThroughReference :
  ∀ {Unitary} (group : UnitaryDefectGroup Unitary) left reference right →
  Telescope.multiply (kernel group)
    (relative group left reference)
    (relative group reference right)
  ≡ relative group left right
relativeFactorThroughReference group left reference right =
  trans
    (associative group
      (relative group left reference)
      reference
      (inverse group right))
    (trans
      (cong
        (λ middle →
          Telescope.multiply (kernel group) left
            (Telescope.multiply (kernel group) middle (inverse group right)))
        (inverseLeft group reference))
      (trans
        (cong
          (Telescope.multiply (kernel group) left)
          (identityLeft group (inverse group right)))
        refl))

relativeDefectTriangleThroughReference :
  ∀ {Unitary} (group : UnitaryDefectGroup Unitary) left reference right →
  Telescope.defect (kernel group) (relative group left right)
  ≤ Telescope.defect (kernel group) (relative group left reference)
    + Telescope.defect (kernel group) (relative group reference right)
relativeDefectTriangleThroughReference group left reference right =
  subst
    (λ selected →
      Telescope.defect (kernel group) selected
      ≤ Telescope.defect (kernel group) (relative group left reference)
        + Telescope.defect (kernel group) (relative group reference right))
    (relativeFactorThroughReference group left reference right)
    (Telescope.productDefectTriangle (kernel group)
      (relative group left reference)
      (relative group reference right))

record SameSelectedContourBall
    {Unitary : Set}
    (group : UnitaryDefectGroup Unitary)
    (input reference centre : Unitary) : Set where
  field
    inputInside :
      Telescope.defect (kernel group) (relative group input reference)
      ≤ Budget.length24OperatorDefectBudget
    centreInside :
      Telescope.defect (kernel group) (relative group reference centre)
      ≤ Budget.length24OperatorDefectBudget

open SameSelectedContourBall public

centreRelativeDefectInsideTwoContourBudget :
  ∀ {Unitary} (group : UnitaryDefectGroup Unitary)
    input reference centre →
  SameSelectedContourBall group input reference centre →
  Telescope.defect (kernel group) (relative group input centre)
  ≤ Budget.relativeTwoContourDefectBudget
centreRelativeDefectInsideTwoContourBudget group input reference centre bounds =
  ℚP.≤-trans
    (relativeDefectTriangleThroughReference group input reference centre)
    (ℚP.+-mono-≤ (inputInside bounds) (centreInside bounds))

centreRelativeDefectInsideCMP98Threshold :
  ∀ {Unitary} (group : UnitaryDefectGroup Unitary)
    input reference centre →
  SameSelectedContourBall group input reference centre →
  Telescope.defect (kernel group) (relative group input centre)
  ≤ Chart.sourceDefectThreshold
centreRelativeDefectInsideCMP98Threshold group input reference centre bounds =
  ℚP.≤-trans
    (centreRelativeDefectInsideTwoContourBudget group input reference centre bounds)
    Budget.relativeTwoContourDefectInsideSourceThreshold

centreRelativeLogInsideSourceYRadius :
  ∀ {Unitary} (group : UnitaryDefectGroup Unitary)
    input reference centre logMagnitude →
  SameSelectedContourBall group input reference centre →
  Chart.PrincipalLogDefectBound
    (Telescope.defect (kernel group) (relative group input centre))
    logMagnitude →
  logMagnitude ≤ Eq38.sourceYRadius
centreRelativeLogInsideSourceYRadius
    group input reference centre logMagnitude ball logBound =
  Chart.defectOneTwentyFourthImpliesYRadius
    (Telescope.defect (kernel group) (relative group input centre))
    logMagnitude
    logBound
    (centreRelativeDefectInsideCMP98Threshold
      group input reference centre ball)

cmp109FederbushCentreRelativeTriangleLevel : ProofLevel
cmp109FederbushCentreRelativeTriangleLevel = machineChecked

cmp109FederbushSameContourBallImpliesSourceChartLevel : ProofLevel
cmp109FederbushSameContourBallImpliesSourceChartLevel = machineChecked

-- The remaining physical G1 producer is exactly the assertion that the actual
-- Federbush centre M({U_j}) belongs to the common selected 3/256 invariant
-- ball.  The relative-product and source-chart arithmetic no longer remain.
cmp109FederbushActualCentreInvariantBallLevel : ProofLevel
cmp109FederbushActualCentreInvariantBallLevel = conditional
