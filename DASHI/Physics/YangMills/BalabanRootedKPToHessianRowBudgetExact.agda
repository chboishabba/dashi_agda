module DASHI.Physics.YangMills.BalabanRootedKPToHessianRowBudgetExact where

------------------------------------------------------------------------
-- ROUND69: ROOTED KP + DERIVATIVE SHELL CONTROL -> HESSIAN ROW BUDGET
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Roman Kotecky and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- David C. Brydges, John Dimock and Thomas R. Hurd,
-- "Estimates on Renormalization Group Transformations",
-- Canadian Journal of Mathematics 50 (1998), 756--793.
-- DOI: 10.4153/CJM-1998-041-5.
--
-- DASHI CONTRIBUTION
--
-- Step V already gives a volume-independent rooted polymer shell budget
--
--      sum_{d<n} rootedShell(d) <= 1/2.
--
-- If the field-derivative seminorm supplies, on the SAME rooted activity,
--
--      hessianRowShell(d) <= c_H * rootedShell(d),
--
-- then every finite Hessian-row partial sum obeys
--
--      sum_{d<n} hessianRowShell(d) <= c_H/2.
--
-- This is the exact bridge from the existing KP coordinate of L7 to the local
-- Hessian row bound consumed by the Round69 Bakry--Emery/Polchinski routes.
-- Crucially, no factor proportional to total lattice volume appears.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact as StepV
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record RootedHessianShellControl (Scale Volume Root : Set) : Set₁ where
  field
    kpShell : StepV.UniformRootedShellBound Scale Volume Root

    hessianRowShell : Scale → Volume → Root → Nat → ℚ
    derivativeConstant : ℚ
    derivativeConstantNonnegative : 0ℚ ≤ derivativeConstant

    hessianShellBelowActivityShell : ∀ scale volume root depth →
      hessianRowShell scale volume root depth
      ≤ derivativeConstant * StepV.rootedShell kpShell scale volume root depth

open RootedHessianShellControl public

hessianRowPartialSum :
  ∀ {Scale Volume Root} →
  RootedHessianShellControl Scale Volume Root →
  Scale → Volume → Root → Nat → ℚ
hessianRowPartialSum dataSet scale volume root zero = 0ℚ
hessianRowPartialSum dataSet scale volume root (suc depth) =
  hessianRowPartialSum dataSet scale volume root depth
  + hessianRowShell dataSet scale volume root depth

hessianPartialBelowScaledRootedPartial :
  ∀ {Scale Volume Root}
    (dataSet : RootedHessianShellControl Scale Volume Root)
    scale volume root depth →
  hessianRowPartialSum dataSet scale volume root depth
  ≤ derivativeConstant dataSet
      * StepV.rootedPartialSum (kpShell dataSet) scale volume root depth
hessianPartialBelowScaledRootedPartial dataSet scale volume root zero =
  subst
    (λ right → 0ℚ ≤ right)
    (ℚRing.solve-∀ (derivativeConstant dataSet))
    ℚP.≤-refl
hessianPartialBelowScaledRootedPartial dataSet scale volume root (suc depth) =
  let
    induction = hessianPartialBelowScaledRootedPartial
      dataSet scale volume root depth
    step = hessianShellBelowActivityShell dataSet scale volume root depth
    summed = ℚP.+-mono-≤ induction step
  in
  subst
    (λ right →
      hessianRowPartialSum dataSet scale volume root depth
        + hessianRowShell dataSet scale volume root depth
      ≤ right)
    (ℚRing.solve-∀
      (derivativeConstant dataSet)
      (StepV.rootedPartialSum (kpShell dataSet) scale volume root depth)
      (StepV.rootedShell (kpShell dataSet) scale volume root depth))
    summed

hessianRowPartialBelowHalfDerivativeConstant :
  ∀ {Scale Volume Root}
    (dataSet : RootedHessianShellControl Scale Volume Root)
    scale volume root depth →
  hessianRowPartialSum dataSet scale volume root depth
  ≤ StepV.half * derivativeConstant dataSet
hessianRowPartialBelowHalfDerivativeConstant dataSet scale volume root depth =
  let
    first = hessianPartialBelowScaledRootedPartial
      dataSet scale volume root depth

    kp = StepV.uniformFiniteVolumeKoteckyPreiss
      (kpShell dataSet) scale volume root depth

    scaled = Norm.scaleNonnegative
      (derivativeConstant dataSet)
      (derivativeConstantNonnegative dataSet)
      kp
  in
  ℚP.≤-trans first
    (subst
      (λ right →
        derivativeConstant dataSet
          * StepV.rootedPartialSum (kpShell dataSet) scale volume root depth
        ≤ right)
      (ℚRing.solve-∀ (derivativeConstant dataSet))
      scaled)

rootedKPToHessianRowBudgetLevel : ProofLevel
rootedKPToHessianRowBudgetLevel = machineChecked

-- Physical L7 seam: prove that the SAME derivative seminorm used in the
-- corrected polymer norm bounds the Hessian row contribution of every rooted
-- polymer shell by c_H times the shell activity.  Once that local inequality is
-- proved, the volume-uniform row budget c_H/2 is automatic.
physicalDerivativeSeminormControlsHessianShellLevel : ProofLevel
physicalDerivativeSeminormControlsHessianShellLevel = conditional
