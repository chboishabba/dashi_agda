module DASHI.Physics.YangMills.BalabanCMP98MinimalContourSelectedYRadiusExact where

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
-- DASHI CONTRIBUTION
--
-- Compose the exact ingredients now available for the G1 base-point radius:
--
--   * minimal selected contour length <= 24;
--   * physical relaxed-radius quaternion l1 bound <= 1/1024 per factor;
--   * unitary operator-defect telescope;
--   * CMP98 equation (25), rationalized by pi/2 <= 2.
--
-- The resulting theorem proves the literal source requirement |Y| <= 1/12
-- once the selected contour factors are identified with the physical SU(2)
-- links and their operator defects are bounded by the already-proved rational
-- quaternion l1 majorant.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact as Chart
import DASHI.Physics.YangMills.BalabanCMP98Equation38PrincipalLogQuadraticExact as Eq38

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ values) = suc (listLength values)

record MinimalSelectedContourYData (Unitary : Set) : Set₁ where
  field
    kernel : Telescope.UnitaryOperatorDefectKernel Unitary
    factors : List Unitary
    lengthAtMost24 : listLength factors ≤ 24

    factorDefectBelowPhysicalMajorant : ∀ factor →
      Telescope.defect kernel factor ≤ Budget.perLinkDefectMajorant

    baseLogMagnitude : ℚ
    equation25ForProduct :
      Chart.PrincipalLogDefectBound
        (Telescope.defect kernel (Telescope.productList kernel factors))
        baseLogMagnitude

open MinimalSelectedContourYData public

selectedContourProductDefectBelowBudget :
  ∀ {Unitary}
    (data : MinimalSelectedContourYData Unitary) →
  Telescope.defect (kernel data)
    (Telescope.productList (kernel data) (factors data))
  ≤ Budget.length24OperatorDefectBudget
selectedContourProductDefectBelowBudget data =
  let
    majorant = λ _ → Budget.perLinkDefectMajorant
    pointwise : Telescope.PointwiseDefectMajorant
      (kernel data) (factors data) majorant
    pointwise = record
      { Telescope.PointwiseDefectMajorant.pointwise =
          factorDefectBelowPhysicalMajorant data }

    telescope = Telescope.productDefectBelowMajorantSum
      (kernel data) (factors data) majorant pointwise

    sumBound = Budget.finiteLength24DefectSum
      (factors data) (lengthAtMost24 data) majorant
      (λ _ → ℚP.≤-refl)
  in
  ℚP.≤-trans telescope sumBound

selectedContourBaseLogInsideEquation38YRadius :
  ∀ {Unitary}
    (data : MinimalSelectedContourYData Unitary) →
  baseLogMagnitude data ≤ Eq38.sourceYRadius
selectedContourBaseLogInsideEquation38YRadius data =
  Budget.length24TelescopingDefectImpliesSourceYRadius
    (Telescope.defect (kernel data)
      (Telescope.productList (kernel data) (factors data)))
    (baseLogMagnitude data)
    (selectedContourProductDefectBelowBudget data)
    (equation25ForProduct data)

cmp98MinimalSelectedContourYRadiusLevel : ProofLevel
cmp98MinimalSelectedContourYRadiusLevel = machineChecked
