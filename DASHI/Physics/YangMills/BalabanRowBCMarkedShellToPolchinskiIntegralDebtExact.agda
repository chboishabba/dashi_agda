module DASHI.Physics.YangMills.BalabanRowBCMarkedShellToPolchinskiIntegralDebtExact where

------------------------------------------------------------------------
-- ROW B -> ROW C: MARKED SHELL -> SAME-SHELL CURVATURE -> POLCHINSKI INTEGRAL
--
-- If a Row-B differentiated marked shell dominates the same-density negative
-- curvature debt, and the actual negative Polchinski-time integral on shell n
-- is bounded by that same curvature debt, then the repository's existing
-- continuous-time summation compiler applies immediately.
--
-- This removes a second possible duplicate summability proof: after the two
-- pointwise same-object inequalities
--
--       I_n <= eta_n <= E_n,
--
-- all finite-cutoff temporal curvature control is downstream algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _*_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanRowBCMarkedShellToCurvatureDebtExact as BC
import DASHI.Physics.YangMills.BalabanRowBActivityEntropyToShellEnergyExact as B
import DASHI.Physics.YangMills.BalabanPolchinskiShellIntegralDebtExact as Integral
import DASHI.Physics.YangMills.BalabanUnifiedPolchinskiCurvatureDebtExact as Curv
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondTailModulusExact as Tail

record MarkedShellPolchinskiIntegralDomination : Set₁ where
  field
    shellCurvature : BC.MarkedShellCurvatureDomination

    shellIntegralDebt : Nat → ℚ
    shellIntegralNonnegative : ∀ n → 0ℚ ≤ shellIntegralDebt n
    shellIntegralBelowCurvature : ∀ n →
      shellIntegralDebt n ≤ BC.curvatureDebt shellCurvature n

open MarkedShellPolchinskiIntegralDomination public

asPolchinskiShellIntegralDebt :
  MarkedShellPolchinskiIntegralDomination → Integral.PolchinskiShellIntegralDebt
asPolchinskiShellIntegralDebt dataSet = record
  { Integral.PolchinskiShellIntegralDebt.discreteDebt =
      BC.asGeometricNegativeCurvatureDebt (shellCurvature dataSet)
  ; Integral.PolchinskiShellIntegralDebt.shellIntegralDebt =
      shellIntegralDebt dataSet
  ; Integral.PolchinskiShellIntegralDebt.shellIntegralNonnegative =
      shellIntegralNonnegative dataSet
  ; Integral.PolchinskiShellIntegralDebt.shellIntegralBelowDiscrete =
      shellIntegralBelowCurvature dataSet
  }

markedShellIntegratedPolchinskiDebtUniformBound :
  (dataSet : MarkedShellPolchinskiIntegralDomination) → ∀ count →
  Integral.finiteIntegratedPolchinskiDebt
    (asPolchinskiShellIntegralDebt dataSet) count
  ≤ Tail.tailFactor
      * B.combinedBaseEnergy (BC.marked (shellCurvature dataSet))
markedShellIntegratedPolchinskiDebtUniformBound dataSet count =
  Integral.finiteIntegratedPolchinskiDebtUniformBound
    (asPolchinskiShellIntegralDebt dataSet) count

rowBCMarkedShellToPolchinskiIntegralCarrierLevel : ProofLevel
rowBCMarkedShellToPolchinskiIntegralCarrierLevel = machineChecked

rowBCMarkedShellToUniformIntegratedCurvatureDebtLevel : ProofLevel
rowBCMarkedShellToUniformIntegratedCurvatureDebtLevel = machineChecked

-- Remaining physical temporal-C seam: on the SAME literal compact-group Gibbs
-- density identify the shell integral I_n and prove I_n <= eta_n.  If Row B's
-- differentiated CMP116 shell also proves eta_n <= E_n, no further temporal
-- summability theorem remains.  Spatial covariant influence is still separate.
literalSameDensityPolchinskiIntegralBelowCurvatureShellLevel : ProofLevel
literalSameDensityPolchinskiIntegralBelowCurvatureShellLevel = conditional
