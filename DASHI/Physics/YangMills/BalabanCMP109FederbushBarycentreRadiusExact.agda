module DASHI.Physics.YangMills.BalabanCMP109FederbushBarycentreRadiusExact where

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
-- Hermann Karcher,
-- "Riemannian Center of Mass and Mollifier Smoothing",
-- Communications on Pure and Applied Mathematics 30 (1977), 509--541.
-- DOI: 10.1002/cpa.3160300502.
--
-- DASHI CONTRIBUTION
--
-- Record the high-slack Karcher-centre route to the final G1 chart without
-- pretending that the source identification has already been checked.
-- For a finite family contained in a geodesically convex r-ball, the standard
-- centre-of-mass comparison gives a 2r radius bound for the minimizing centre.
-- At the literal selected contour radius r = 3/256,
--
--        2r = 3/128 = 18/768 < 23/768,
--
-- while 23/768 is the full remaining operator-defect allowance before the
-- CMP98 1/24 source threshold is exhausted.
--
-- The exact rational comparison below is machine algebra.  The geometric
-- centre-of-mass radius theorem is standard imported mathematics.  The only
-- source-specific G1 seam left on this route is identification of Bałaban's
-- local solution of sum_j log(U_j V^-1)=0 with that unique convex Karcher
-- centre, together with the SU(2) geodesic/operator-defect comparison in the
-- selected chart.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanCMP109FederbushCentreMaximalChartBudgetExact as Maximal

selectedTwiceContourRadius : ℚ
selectedTwiceContourRadius = (+ 2 / 1) * Budget.length24OperatorDefectBudget

selectedTwiceContourRadiusIsThree128 :
  selectedTwiceContourRadius ≡ + 3 / 128
selectedTwiceContourRadiusIsThree128 = ℚRing.solve []

selectedTwiceContourFitsMaximalCentreAllowance :
  selectedTwiceContourRadius ≤ Maximal.centreMaximalAllowance
selectedTwiceContourFitsMaximalCentreAllowance =
  ℚP.<⇒≤
    (ℚP.positive⁻¹
      (Maximal.centreMaximalAllowance - selectedTwiceContourRadius))

cmp109SelectedTwiceRadiusFitsMaximalChartLevel : ProofLevel
cmp109SelectedTwiceRadiusFitsMaximalChartLevel = machineChecked

-- Standard finite Riemannian centre-of-mass result in a strongly convex ball.
cmp109FiniteKarcherCentreTwiceRadiusLevel : ProofLevel
cmp109FiniteKarcherCentreTwiceRadiusLevel = standardImported

-- These two declarations are deliberately not promoted by the generic Karcher
-- theorem.  They are the literal Bałaban/SU(2) source identifications still to
-- be instantiated on the selected contour family.
cmp109FederbushKarcherIdentificationLevel : ProofLevel
cmp109FederbushKarcherIdentificationLevel = conditional

cmp109FederbushGeodesicToOperatorDefectComparisonLevel : ProofLevel
cmp109FederbushGeodesicToOperatorDefectComparisonLevel = conditional
