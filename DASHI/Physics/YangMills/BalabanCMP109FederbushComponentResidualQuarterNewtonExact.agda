module DASHI.Physics.YangMills.BalabanCMP109FederbushComponentResidualQuarterNewtonExact where

-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042.
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I", CMP 109 (1987), 249--301. DOI: 10.1007/BF01215223.

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanCMP109FederbushResidualMassTelescopeExact as Residual
import DASHI.Physics.YangMills.BalabanCMP109FederbushQuarterNewtonBudgetExact as Newton
import DASHI.Physics.YangMills.BalabanCMP109FederbushMaximalQuarterInvariantBallExact as Ball

reopenedSelectedComponentResidual : ℚ
reopenedSelectedComponentResidual =
  Reopen.fourThirds * Residual.selectedFederbushComponentResidualBudget

selectedComponentResidualBelowThreeSixteenths :
  Residual.selectedFederbushComponentResidualBudget ≤ Newton.threeSixteenths
selectedComponentResidualBelowThreeSixteenths =
  Norm.nonnegativeDifferenceImpliesBelow
    (ℚP.nonNegative⁻¹
      (Newton.threeSixteenths - Residual.selectedFederbushComponentResidualBudget))

reopenedSelectedComponentResidualIsFiveOver49152 :
  reopenedSelectedComponentResidual ≡ + 5 / 49152
reopenedSelectedComponentResidualIsFiveOver49152 = ℚRing.solve []

reopenedSelectedComponentResidualFitsQuarter :
  reopenedSelectedComponentResidual ≤ Ball.quarter
reopenedSelectedComponentResidualFitsQuarter =
  Norm.nonnegativeDifferenceImpliesBelow
    (ℚP.nonNegative⁻¹ (Ball.quarter - reopenedSelectedComponentResidual))

cmp109FederbushComponentResidualQuarterNewtonArithmeticLevel : ProofLevel
cmp109FederbushComponentResidualQuarterNewtonArithmeticLevel = machineChecked

cmp109FederbushNewtonDerivativeIsComponentResidualLevel : ProofLevel
cmp109FederbushNewtonDerivativeIsComponentResidualLevel = conditional
