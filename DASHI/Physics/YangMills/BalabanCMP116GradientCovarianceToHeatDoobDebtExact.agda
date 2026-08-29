{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116GradientCovarianceToHeatDoobDebtExact where

------------------------------------------------------------------------
-- ROUND102 B->C TEMPORAL CAPSTONE
--
-- The static term of the log/Doob Hessian is represented by the SAME CMP116
-- physical Hessian shell.  Round102 reduces the genuine covariance correction
-- to first-gradient marked Cauchy data.  This file composes those two facts with
-- the existing Heat/Doob covariance-debt compiler.
--
-- After this composition the temporal Yang--Mills input is only:
--   1. literal same-density identification of the conditional/static Hessian
--      response with the CMP116 hessian mark;
--   2. literal first-gradient covariance inequality on that same density/common
--      analytic domain.
-- All 1/2 shell decay, 17/32 promotion and cumulative curvature summation are
-- downstream theorem-owned algebra.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanHeatDoobGradientCovarianceMarkedCauchyExact as Grad
import DASHI.Physics.YangMills.BalabanHeatDoobHessianCovarianceDebtExact as Heat

record CMP116GradientCovarianceHeatDoobTemporalData
    (Scale Volume Root : Set) : Set₁ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    gradientCovariance : Grad.HeatDoobTemporalGradientCovariance

    actualNegativeHessianDebt : Nat → ℚ
    actualNonnegative : ∀ n → 0ℚ ≤ actualNegativeHessianDebt n

    -- Literal log/Doob differential inequality after the conditional/static
    -- Hessian term has been identified with the CMP116 hessian mark.
    heatDoobSplit : ∀ n →
      actualNegativeHessianDebt n
      ≤ Shared.hessianInfluenceShell shared scale volume root n
        + Grad.covarianceDebt gradientCovariance n

open CMP116GradientCovarianceHeatDoobTemporalData public

asHeatDoobHessianCovarianceDebt :
  ∀ {Scale Volume Root} →
  CMP116GradientCovarianceHeatDoobTemporalData Scale Volume Root →
  Heat.HeatDoobHessianCovarianceDebt Scale Volume Root
asHeatDoobHessianCovarianceDebt dataSet = record
  { Heat.HeatDoobHessianCovarianceDebt.shared = shared dataSet
  ; Heat.HeatDoobHessianCovarianceDebt.scale = scale dataSet
  ; Heat.HeatDoobHessianCovarianceDebt.volume = volume dataSet
  ; Heat.HeatDoobHessianCovarianceDebt.root = root dataSet
  ; Heat.HeatDoobHessianCovarianceDebt.staticHessianDebt =
      Shared.hessianInfluenceShell (shared dataSet) (scale dataSet) (volume dataSet) (root dataSet)
  ; Heat.HeatDoobHessianCovarianceDebt.covarianceDebt =
      Grad.covarianceDebt (gradientCovariance dataSet)
  ; Heat.HeatDoobHessianCovarianceDebt.actualNegativeHessianDebt =
      actualNegativeHessianDebt dataSet
  ; Heat.HeatDoobHessianCovarianceDebt.staticNonnegative =
      Shared.hessianInfluenceShellNonnegative
        (shared dataSet) (scale dataSet) (volume dataSet) (root dataSet)
  ; Heat.HeatDoobHessianCovarianceDebt.covarianceNonnegative =
      Grad.covarianceDebtNonnegative (gradientCovariance dataSet)
  ; Heat.HeatDoobHessianCovarianceDebt.actualNonnegative = actualNonnegative dataSet
  ; Heat.HeatDoobHessianCovarianceDebt.heatDoobSplit = heatDoobSplit dataSet
  ; Heat.HeatDoobHessianCovarianceDebt.staticBelowMarkedHessian = λ n →
      Data.Rational.Properties.≤-refl
  ; Heat.HeatDoobHessianCovarianceDebt.covarianceAmplitude =
      Grad.temporalCovarianceAmplitude (gradientCovariance dataSet)
  ; Heat.HeatDoobHessianCovarianceDebt.covarianceAmplitudeNonnegative =
      Grad.temporalCovarianceAmplitudeNonnegative (gradientCovariance dataSet)
  ; Heat.HeatDoobHessianCovarianceDebt.covarianceGeometricHalf =
      Grad.temporalCovarianceGeometricHalf (gradientCovariance dataSet)
  }

finiteHeatDoobDebtFromCMP116Gradients :
  ∀ {Scale Volume Root}
    (dataSet : CMP116GradientCovarianceHeatDoobTemporalData Scale Volume Root)
    count →
  DASHI.Physics.YangMills.BalabanUnifiedPolchinskiCurvatureDebtExact.finiteCurvatureDebt
    (Heat.asGeometricNegativeCurvatureDebt (asHeatDoobHessianCovarianceDebt dataSet)) count
  ≤ DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondTailModulusExact.tailFactor
      * Heat.combinedAmplitude (asHeatDoobHessianCovarianceDebt dataSet)
finiteHeatDoobDebtFromCMP116Gradients dataSet =
  Heat.finiteActualHeatDoobDebtUniform (asHeatDoobHessianCovarianceDebt dataSet)

cmp116GradientCovarianceToHeatDoobDebtLevel : ProofLevel
cmp116GradientCovarianceToHeatDoobDebtLevel = machineChecked

-- The remaining conditional statement is now literal source identification,
-- not a fresh summability estimate.
literalCMP116GradientHeatDoobTemporalInstantiationLevel : ProofLevel
literalCMP116GradientHeatDoobTemporalInstantiationLevel = conditional
