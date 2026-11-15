module DASHI.Moonshine.AbelBishopMachinQuarterToQPeriodExact where

------------------------------------------------------------------------
-- THE ACTUAL BISHOP QUARTER-MACHIN ANGLE IN THE ORIGINAL q SOURCE
--
-- Reuse the established Bishop Machin arctangent and quarter-angle
-- theorem; no second pi constant or numerical approximation is introduced.
--
-- Remaining analytic obligation: identify this same Bishop angle with
-- the trig period (and prove original complex exponential additivity).
-- The equations here are Bishop setoid algebra, not exp(2*pi*i)=1.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)

import Real as Bishop
import RealProperties as BishopP
import DASHI.Foundations.BishopMachinArctanConstructionExact as Machin
import DASHI.Foundations.BishopMachinQuarterAngleBranchExact as Quarter
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Round11
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Cutset
import DASHI.Analysis.BishopSetoidComplexExact as Complex
import DASHI.Moonshine.AbelBishopOriginalQParameterExact as Q

two four eight : Bishop.ℝ
two = Bishop._⋆ (+ 2 / 1)
four = Bishop._⋆ (+ 4 / 1)
eight = Bishop._⋆ (+ 8 / 1)

machinTwoPi : Bishop.ℝ
machinTwoPi = Bishop._*_ two Machin.bishopMachinPi

machinEightQuarter : Bishop.ℝ
machinEightQuarter = Bishop._*_ eight Quarter.machinQuarterAngle

machinTwoPiIsTwiceFourQuarter :
  Bishop._≃_ machinTwoPi
    (Bishop._*_ two (Bishop._*_ four Quarter.machinQuarterAngle))
machinTwoPiIsTwiceFourQuarter =
  BishopP.*-cong
    BishopP.≃-refl
    (BishopP.≃-symm Quarter.fourTimesQuarterIsMachinPi)

twiceFourQuarterIsEightQuarter :
  Bishop._≃_
    (Bishop._*_ two (Bishop._*_ four Quarter.machinQuarterAngle))
    machinEightQuarter
twiceFourQuarterIsEightQuarter =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ theta →
      (Κ (+ 2 / 1) ⊗ (Κ (+ 4 / 1) ⊗ theta))
      ⊜ (Κ (+ 8 / 1) ⊗ theta))
    BishopP.≃-refl Quarter.machinQuarterAngle

originalBishopTwoPiEqualsEightMachinQuarter :
  Bishop._≃_ machinTwoPi machinEightQuarter
originalBishopTwoPiEqualsEightMachinQuarter =
  BishopP.≃-trans
    machinTwoPiIsTwiceFourQuarter
    twiceFourQuarterIsEightQuarter

originalRound11QPiIsActualMachin :
  (inputs : Cutset.Round11BishopCutset) →
  Bishop._≃_
    (Complex.pi (Round11.round11MachinTranscendentals inputs))
    Machin.bishopMachinPi
originalRound11QPiIsActualMachin inputs = BishopP.≃-refl

originalRound11SelectedTwoPiIsEightMachinQuarter :
  (inputs : Cutset.Round11BishopCutset) →
  Bishop._≃_
    (Bishop._*_ two
      (Complex.pi (Round11.round11MachinTranscendentals inputs)))
    machinEightQuarter
originalRound11SelectedTwoPiIsEightMachinQuarter inputs =
  BishopP.≃-trans
    (BishopP.*-cong
      BishopP.≃-refl
      (originalRound11QPiIsActualMachin inputs))
    originalBishopTwoPiEqualsEightMachinQuarter

-- Source ownership of q is unchanged: it is the real original expC
-- selected at the same Round11 sine/cosine data and Bishop Machin pi.
originalRound11QIsOriginalBishopExpression :
  (inputs : Cutset.Round11BishopCutset) →
  (tau : Complex.BishopComplex) →
  Complex._≈C_
    (Q.originalRound11MachinQAt inputs tau)
    (Q.originalBishopQAt
      (Round11.round11MachinTranscendentals inputs) tau)
originalRound11QIsOriginalBishopExpression inputs tau =
  Complex.≈C-refl _
