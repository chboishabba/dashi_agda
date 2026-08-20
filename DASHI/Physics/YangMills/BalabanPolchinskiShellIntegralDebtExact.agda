module DASHI.Physics.YangMills.BalabanPolchinskiShellIntegralDebtExact where

------------------------------------------------------------------------
-- ROUND83: PER-SHELL POLCHINSKI INTEGRALS -> UNIFORM TOTAL CURVATURE DEBT
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Roland Bauerschmidt and Thierry Bodineau,
-- "Log-Sobolev Inequality for the Continuum Sine-Gordon Model",
-- Communications on Pure and Applied Mathematics 74 (2021), 2064--2113.
-- DOI: 10.1002/cpa.21926.
--
-- Roland Bauerschmidt, Thierry Bodineau and Benoit Dagallier,
-- "Stochastic dynamics and the Polchinski equation: an introduction",
-- Probability Surveys 21 (2024), 200--290.
-- DOI: 10.1214/24-PS27.
--
-- David C. Brydges, John Dimock and Thomas R. Hurd,
-- "Estimates on Renormalization Group Transformations",
-- Canadian Journal of Mathematics 50 (1998), 756--793.
-- DOI: 10.4153/CJM-1998-041-5.
--
-- DASHI CONTRIBUTION
--
-- The earlier curvature module deliberately left the conversion from a discrete
-- RG-shell debt to the continuous Polchinski-time integral opaque.  The shortest
-- route does not need such an opaque global comparison.
--
-- Let eta_n be the already controlled negative-curvature debt of shell n, with
--
--       eta_n <= C (17/32)^n.
--
-- Let I_n be the ACTUAL integral of the negative Polchinski curvature over the
-- corresponding continuous time interval.  If one proves only the local
-- same-shell estimate
--
--       0 <= I_n <= eta_n,
--
-- then I_n itself is a GeometricNegativeCurvatureDebt with the same amplitude C.
-- The existing exact geometric theorem therefore yields, for every finite
-- cutoff m,
--
--       sum_{n<m} I_n <= (32/15) C.
--
-- Hence B1's continuous-time part is reduced to a per-shell integral estimate;
-- no additional infinite-time summation theorem or cutoff-dependent comparison
-- is required.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanUnifiedPolchinskiCurvatureDebtExact as Curv
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondTailModulusExact as Tail

record PolchinskiShellIntegralDebt : Set₁ where
  field
    discreteDebt : Curv.GeometricNegativeCurvatureDebt

    -- I_n is the integral of the negative part over the n-th Polchinski-time
    -- shell.  Integration itself remains in the physical/analytic carrier;
    -- this theorem begins once its nonnegative scalar value is available.
    shellIntegralDebt : Nat → ℚ
    shellIntegralNonnegative : ∀ n → 0ℚ ≤ shellIntegralDebt n
    shellIntegralBelowDiscrete : ∀ n →
      shellIntegralDebt n ≤ Curv.debtAtScale discreteDebt n

open PolchinskiShellIntegralDebt public

integratedDebtAsGeometricDebt :
  PolchinskiShellIntegralDebt → Curv.GeometricNegativeCurvatureDebt
integratedDebtAsGeometricDebt dataSet = record
  { Curv.GeometricNegativeCurvatureDebt.debtAtScale = shellIntegralDebt dataSet
  ; Curv.GeometricNegativeCurvatureDebt.debtNonnegative =
      shellIntegralNonnegative dataSet
  ; Curv.GeometricNegativeCurvatureDebt.amplitude =
      Curv.amplitude (discreteDebt dataSet)
  ; Curv.GeometricNegativeCurvatureDebt.amplitudeNonnegative =
      Curv.amplitudeNonnegative (discreteDebt dataSet)
  ; Curv.GeometricNegativeCurvatureDebt.geometricDebtBound =
      λ n →
        ℚP.≤-trans
          (shellIntegralBelowDiscrete dataSet n)
          (Curv.geometricDebtBound (discreteDebt dataSet) n)
  }

finiteIntegratedPolchinskiDebt :
  PolchinskiShellIntegralDebt → Nat → ℚ
finiteIntegratedPolchinskiDebt dataSet =
  Curv.finiteCurvatureDebt (integratedDebtAsGeometricDebt dataSet)

finiteIntegratedPolchinskiDebtUniformBound :
  (dataSet : PolchinskiShellIntegralDebt) → ∀ count →
  finiteIntegratedPolchinskiDebt dataSet count
  ≤ Tail.tailFactor * Curv.amplitude (discreteDebt dataSet)
finiteIntegratedPolchinskiDebtUniformBound dataSet =
  Curv.finiteCurvatureDebtUniformBound
    (integratedDebtAsGeometricDebt dataSet)

polchinskiShellIntegralDebtCompilerLevel : ProofLevel
polchinskiShellIntegralDebtCompilerLevel = machineChecked

-- The physical B1 remainder is now local in RG time: prove that the actual
-- negative curvature integral over each Polchinski time shell is bounded by the
-- SAME shell debt produced from the differentiated Balaban effective activity.
-- Uniform summability is no longer an independent analytic task.
physicalPolchinskiPerShellIntegralBelowMarkedDebtLevel : ProofLevel
physicalPolchinskiPerShellIntegralBelowMarkedDebtLevel = conditional
