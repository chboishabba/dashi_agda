module DASHI.Physics.YangMills.BalabanCMP109FederbushKarcherCorrectedRadiusExact where

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
-- Correct a subtle norm issue in the barycentre shortcut.  The selected
-- contour certificate is an OPERATOR-DEFECT radius 3/256, while Karcher's
-- centre theorem uses geodesic distance.  They must not be silently identified.
--
-- The exact budget needed is very mild.  It suffices to prove, on the selected
-- SU(2) principal chart,
--
--   d_geo(I,U) <= (5/4) ||U-I||_op.                 (* )
--
-- Then every selected contour lies in geodesic radius
--
--   (5/4)(3/256) = 15/1024.
--
-- A twice-radius Karcher estimate gives
--
--   d_geo(R,V) <= 15/512.
--
-- Finally ||RV^-1-I||_op <= d_geo(R,V), and
--
--   15/512 + 1/1536 = 23/768.
--
-- Thus the Karcher route really does fit the full CMP98 centre allowance, but
-- with only 1/1536 of slack after the explicit metric conversion.  The direct
-- quarter-Newton route remains preferable unless (*) is cheaper to instantiate.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact as Contour
import DASHI.Physics.YangMills.BalabanCMP109FederbushCentreMaximalChartBudgetExact as Centre

operatorToGeodesicFactor : ℚ
operatorToGeodesicFactor = + 5 / 4

selectedGeodesicContourRadius : ℚ
selectedGeodesicContourRadius =
  operatorToGeodesicFactor * Contour.length24OperatorDefectBudget

karcherTwiceGeodesicRadius : ℚ
karcherTwiceGeodesicRadius = (+ 2 / 1) * selectedGeodesicContourRadius

karcherCentreSlack : ℚ
karcherCentreSlack = + 1 / 1536

selectedGeodesicContourRadiusIs15Over1024 :
  selectedGeodesicContourRadius ≡ + 15 / 1024
selectedGeodesicContourRadiusIs15Over1024 = ℚRing.solve []

karcherTwiceGeodesicRadiusIs15Over512 :
  karcherTwiceGeodesicRadius ≡ + 15 / 512
karcherTwiceGeodesicRadiusIs15Over512 = ℚRing.solve []

karcherCorrectedRadiusPlusSlackIsMaximalAllowance :
  karcherTwiceGeodesicRadius + karcherCentreSlack
  ≡ Centre.centreMaximalAllowance
karcherCorrectedRadiusPlusSlackIsMaximalAllowance = ℚRing.solve []

karcherCorrectedRadiusFitsMaximalAllowance :
  karcherTwiceGeodesicRadius ≤ Centre.centreMaximalAllowance
karcherCorrectedRadiusFitsMaximalAllowance =
  ℚP.p≤p+q karcherTwiceGeodesicRadius karcherCentreSlack
    (ℚP.nonNegative⁻¹ karcherCentreSlack)

cmp109KarcherCorrectedRadiusArithmeticLevel : ProofLevel
cmp109KarcherCorrectedRadiusArithmeticLevel = machineChecked

-- SU(2) analytic metric leaf: on the selected principal chart prove
-- d_geo(I,U) <= (5/4)||U-I||_op.  For U with principal angle theta this is the
-- elementary inequality theta <= (5/2) sin(theta/2); the repository's Bishop
-- sine-series lane is the intended constructive proof.
cmp109SelectedOperatorDefectToGeodesicFiveFourthLevel : ProofLevel
cmp109SelectedOperatorDefectToGeodesicFiveFourthLevel = conditional

-- Standard strongly-convex-ball centre theorem and the gradient identification
-- sum_j log(U_j V^-1)=0 = Karcher critical-point equation.
cmp109FederbushKarcherCriticalPointIdentificationLevel : ProofLevel
cmp109FederbushKarcherCriticalPointIdentificationLevel = standardImported
