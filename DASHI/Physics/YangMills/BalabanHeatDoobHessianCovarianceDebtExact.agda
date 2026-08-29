{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanHeatDoobHessianCovarianceDebtExact where

------------------------------------------------------------------------
-- ROUND101 CORRECTION: HEAT/DOOB HESSIAN IS NOT GENERALLY THE STATIC HESSIAN
--
-- The tempting Round100 same-object shortcut eta_n = H_n is too strong in a
-- genuine Doob/heat interpolation.  Differentiating a log heat average produces
-- a conditional expected Hessian term AND a covariance-of-gradients term.
-- Therefore a static CMP116 Hessian shell does not, by itself, dominate the
-- negative Hessian of the heat-renormalised potential.
--
-- BIDI replacement:
--
--   forward CMP116 gives the geometric static-Hessian debt H_n;
--   backward Heat/Doob needs the actual negative curvature debt eta_n;
--   the exact middle object is a covariance split
--
--       eta_n <= H_n + Cov_n.
--
-- If both pieces decay with the already-owned 1/2 shell ratio, then eta_n has
-- the same ratio with amplitude A_H + A_Cov.  Since 1/2 <= 17/32, the existing
-- curvature-debt summation applies unchanged.  Thus the new physical leaf is a
-- quantitative covariance estimate, not a false equality eta=H.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondIterationExact as Iter
import DASHI.Physics.YangMills.BalabanUnifiedPolchinskiCurvatureDebtExact as Curv
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondTailModulusExact as Tail
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact as Geom

halfBelowTheta : Geo.half ≤ Iter.theta
halfBelowTheta = toWitness {a? = Geo.half ℚP.≤? Iter.theta} _

halfPowerBelowThetaPower : ∀ n → Geo.halfPower n ≤ Iter.thetaPower n
halfPowerBelowThetaPower zero = ℚP.≤-refl
halfPowerBelowThetaPower (suc n) =
  ℚP.*-mono-≤
    Geo.halfNonnegative halfBelowTheta
    (Geo.halfPowerNonnegative n)
    (halfPowerBelowThetaPower n)

record HeatDoobHessianCovarianceDebt
    (Scale Volume Root : Set) : Set₁ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    staticHessianDebt covarianceDebt actualNegativeHessianDebt : Nat → ℚ
    staticNonnegative : ∀ n → 0ℚ ≤ staticHessianDebt n
    covarianceNonnegative : ∀ n → 0ℚ ≤ covarianceDebt n
    actualNonnegative : ∀ n → 0ℚ ≤ actualNegativeHessianDebt n

    -- Exact differential/probabilistic bridge after scalar majorisation of the
    -- conditional Hessian and covariance terms.
    heatDoobSplit : ∀ n →
      actualNegativeHessianDebt n
      ≤ staticHessianDebt n + covarianceDebt n

    -- The static term is the one controlled by the CMP116 physical Hessian mark.
    staticBelowMarkedHessian : ∀ n →
      staticHessianDebt n
      ≤ Shared.hessianInfluenceShell shared scale volume root n

    -- The genuinely additional stochastic term.  It is kept with its own
    -- amplitude rather than hidden in the static Hessian identity.
    covarianceAmplitude : ℚ
    covarianceAmplitudeNonnegative : 0ℚ ≤ covarianceAmplitude
    covarianceGeometricHalf : ∀ n →
      covarianceDebt n ≤ covarianceAmplitude * Geo.halfPower n

open HeatDoobHessianCovarianceDebt public

combinedAmplitude :
  ∀ {Scale Volume Root} →
  HeatDoobHessianCovarianceDebt Scale Volume Root → ℚ
combinedAmplitude dataSet =
  Geom.markedBaseEnergy (shared dataSet) Shared.hessianMark
    + covarianceAmplitude dataSet

combinedAmplitudeNonnegative :
  ∀ {Scale Volume Root}
    (dataSet : HeatDoobHessianCovarianceDebt Scale Volume Root) →
  0ℚ ≤ combinedAmplitude dataSet
combinedAmplitudeNonnegative dataSet =
  ℚP.+-mono-≤
    (Geom.markedBaseEnergyNonnegative (shared dataSet) Shared.hessianMark)
    (covarianceAmplitudeNonnegative dataSet)

staticGeometricHalf :
  ∀ {Scale Volume Root}
    (dataSet : HeatDoobHessianCovarianceDebt Scale Volume Root) n →
  staticHessianDebt dataSet n
  ≤ Geom.markedBaseEnergy (shared dataSet) Shared.hessianMark
      * Geo.halfPower n
staticGeometricHalf dataSet n =
  ℚP.≤-trans
    (staticBelowMarkedHessian dataSet n)
    (Geom.hessianInfluenceGeometricHalf
      (shared dataSet) (scale dataSet) (volume dataSet) (root dataSet) n)

actualGeometricHalf :
  ∀ {Scale Volume Root}
    (dataSet : HeatDoobHessianCovarianceDebt Scale Volume Root) n →
  actualNegativeHessianDebt dataSet n
  ≤ combinedAmplitude dataSet * Geo.halfPower n
actualGeometricHalf dataSet n =
  let
    split = heatDoobSplit dataSet n
    pieces = ℚP.+-mono-≤
      (staticGeometricHalf dataSet n)
      (covarianceGeometricHalf dataSet n)
  in
  ℚP.≤-trans split
    (subst
      (λ right →
        Geom.markedBaseEnergy (shared dataSet) Shared.hessianMark
            * Geo.halfPower n
          + covarianceAmplitude dataSet * Geo.halfPower n
        ≤ right)
      (ℚRing.solve-∀
        (Geom.markedBaseEnergy (shared dataSet) Shared.hessianMark)
        (covarianceAmplitude dataSet)
        (Geo.halfPower n))
      pieces)

actualGeometricSeventeenThirtySecond :
  ∀ {Scale Volume Root}
    (dataSet : HeatDoobHessianCovarianceDebt Scale Volume Root) n →
  actualNegativeHessianDebt dataSet n
  ≤ combinedAmplitude dataSet * Iter.thetaPower n
actualGeometricSeventeenThirtySecond dataSet n =
  ℚP.≤-trans
    (actualGeometricHalf dataSet n)
    (Norm.scaleNonnegative
      (combinedAmplitude dataSet)
      (combinedAmplitudeNonnegative dataSet)
      (halfPowerBelowThetaPower n))

asGeometricNegativeCurvatureDebt :
  ∀ {Scale Volume Root} →
  HeatDoobHessianCovarianceDebt Scale Volume Root →
  Curv.GeometricNegativeCurvatureDebt
asGeometricNegativeCurvatureDebt dataSet = record
  { Curv.GeometricNegativeCurvatureDebt.debtAtScale =
      actualNegativeHessianDebt dataSet
  ; Curv.GeometricNegativeCurvatureDebt.debtNonnegative =
      actualNonnegative dataSet
  ; Curv.GeometricNegativeCurvatureDebt.amplitude = combinedAmplitude dataSet
  ; Curv.GeometricNegativeCurvatureDebt.amplitudeNonnegative =
      combinedAmplitudeNonnegative dataSet
  ; Curv.GeometricNegativeCurvatureDebt.geometricDebtBound =
      actualGeometricSeventeenThirtySecond dataSet
  }

finiteActualHeatDoobDebtUniform :
  ∀ {Scale Volume Root}
    (dataSet : HeatDoobHessianCovarianceDebt Scale Volume Root) count →
  Curv.finiteCurvatureDebt (asGeometricNegativeCurvatureDebt dataSet) count
  ≤ Tail.tailFactor * combinedAmplitude dataSet
finiteActualHeatDoobDebtUniform dataSet =
  Curv.finiteCurvatureDebtUniformBound
    (asGeometricNegativeCurvatureDebt dataSet)

heatDoobHessianCovarianceSplitCompilerLevel : ProofLevel
heatDoobHessianCovarianceSplitCompilerLevel = machineChecked

heatDoobCovarianceDebtToUniformCurvatureLevel : ProofLevel
heatDoobCovarianceDebtToUniformCurvatureLevel = machineChecked

-- Physical Row-C temporal leaf after the correction:
--   1. identify the conditional/expected Hessian term with/below the SAME CMP116
--      hessian mark;
--   2. prove the gradient-covariance term has a cutoff/volume-uniform geometric
--      half-shell amplitude on the same density.
-- The static identity eta=H is not assumed.
literalHeatDoobCovarianceSplitInstantiationLevel : ProofLevel
literalHeatDoobCovarianceSplitInstantiationLevel = conditional
