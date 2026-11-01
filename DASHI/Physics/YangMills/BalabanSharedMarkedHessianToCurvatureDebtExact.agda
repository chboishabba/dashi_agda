{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSharedMarkedHessianToCurvatureDebtExact where

------------------------------------------------------------------------
-- ROW B -> ROW C: THE SHARED HESSIAN MARK ALREADY DECAYS FASTER THAN 17/32
--
-- The shared CMP116 marked-source control now gives, theorem-exactly,
--
--   H_n <= (C_H/4) (1/2)^n.
--
-- Since 1/2 <= 17/32, any SAME-density negative curvature shell eta_n with
--
--   eta_n <= H_n
--
-- automatically satisfies the repository's existing curvature-debt envelope
--
--   eta_n <= (C_H/4) (17/32)^n.
--
-- Thus the temporal/summability half of Row C does not require a second decay
-- theorem if the literal Heat/Doob negative Hessian shell is pointwise dominated
-- by the already-required physical Hessian mark from Row B.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Decidable using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticGeometricShellExact as Geom
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondIterationExact as Iter
import DASHI.Physics.YangMills.BalabanUnifiedPolchinskiCurvatureDebtExact as Curv
import DASHI.Physics.YangMills.BalabanUnifiedSeventeenThirtySecondTailModulusExact as Tail

halfBelowTheta : Geo.half ≤ Iter.theta
halfBelowTheta = toWitness {a? = Geo.half ℚP.≤? Iter.theta} _

halfPowerBelowThetaPower : ∀ depth →
  Geo.halfPower depth ≤ Iter.thetaPower depth
halfPowerBelowThetaPower zero = ℚP.≤-refl
halfPowerBelowThetaPower (suc depth) =
  ℚP.*-mono-≤
    Geo.halfNonnegative halfBelowTheta
    (Geo.halfPowerNonnegative depth)
    (halfPowerBelowThetaPower depth)

record SharedHessianCurvatureDomination
    (Scale Volume Root : Set) : Set₁ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root

    curvatureDebt : Nat → ℚ
    curvatureDebtNonnegative : ∀ depth → 0ℚ ≤ curvatureDebt depth

    -- THIS is the physical same-density cross-pollination seam.
    curvatureBelowPhysicalHessianMark : ∀ depth →
      curvatureDebt depth
      ≤ Shared.hessianInfluenceShell shared scale volume root depth

open SharedHessianCurvatureDomination public

curvatureBelowSeventeenThirtySecond :
  ∀ {Scale Volume Root}
    (dataSet : SharedHessianCurvatureDomination Scale Volume Root)
    depth →
  curvatureDebt dataSet depth
  ≤ Geom.markedBaseEnergy (shared dataSet) Shared.hessianMark
      * Iter.thetaPower depth
curvatureBelowSeventeenThirtySecond dataSet depth =
  let
    source = shared dataSet
    base = Geom.markedBaseEnergy source Shared.hessianMark

    first = curvatureBelowPhysicalHessianMark dataSet depth
    second = Geom.hessianInfluenceGeometricHalf source
      (scale dataSet) (volume dataSet) (root dataSet) depth

    powerScaled = Norm.scaleNonnegative
      base
      (Geom.markedBaseEnergyNonnegative source Shared.hessianMark)
      (halfPowerBelowThetaPower depth)
  in
  ℚP.≤-trans first (ℚP.≤-trans second powerScaled)

asGeometricNegativeCurvatureDebt :
  ∀ {Scale Volume Root} →
  SharedHessianCurvatureDomination Scale Volume Root →
  Curv.GeometricNegativeCurvatureDebt
asGeometricNegativeCurvatureDebt dataSet = record
  { Curv.GeometricNegativeCurvatureDebt.debtAtScale = curvatureDebt dataSet
  ; Curv.GeometricNegativeCurvatureDebt.debtNonnegative =
      curvatureDebtNonnegative dataSet
  ; Curv.GeometricNegativeCurvatureDebt.amplitude =
      Geom.markedBaseEnergy (shared dataSet) Shared.hessianMark
  ; Curv.GeometricNegativeCurvatureDebt.amplitudeNonnegative =
      Geom.markedBaseEnergyNonnegative (shared dataSet) Shared.hessianMark
  ; Curv.GeometricNegativeCurvatureDebt.geometricDebtBound =
      curvatureBelowSeventeenThirtySecond dataSet
  }

sharedHessianPaysUniformCurvatureDebt :
  ∀ {Scale Volume Root}
    (dataSet : SharedHessianCurvatureDomination Scale Volume Root)
    count →
  Curv.finiteCurvatureDebt (asGeometricNegativeCurvatureDebt dataSet) count
  ≤ Tail.tailFactor
      * Geom.markedBaseEnergy (shared dataSet) Shared.hessianMark
sharedHessianPaysUniformCurvatureDebt dataSet count =
  Curv.finiteCurvatureDebtUniformBound
    (asGeometricNegativeCurvatureDebt dataSet) count

sharedHessianHalfDecayToSeventeenThirtySecondLevel : ProofLevel
sharedHessianHalfDecayToSeventeenThirtySecondLevel = machineChecked

sharedHessianToUniformCurvatureDebtLevel : ProofLevel
sharedHessianToUniformCurvatureDebtLevel = machineChecked

-- Physical seam: prove that the same-density Heat/Doob negative Hessian shell
-- is bounded pointwise by the literal CMP116 hessian mark on the same generated
-- Yang--Mills density.  Once that same-object domination lands, temporal debt is
-- downstream and only Row-C spatial influence/clustering remains independent.
literalSameDensityCurvatureBelowSharedHessianMarkLevel : ProofLevel
literalSameDensityCurvatureBelowSharedHessianMarkLevel = conditional
