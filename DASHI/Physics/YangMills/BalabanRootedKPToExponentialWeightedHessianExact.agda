module DASHI.Physics.YangMills.BalabanRootedKPToExponentialWeightedHessianExact where

------------------------------------------------------------------------
-- ROUND70: ROOTED DYADIC KP -> EXPONENTIALLY WEIGHTED HESSIAN ROW
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
-- Hao Shen, Rongchan Zhu and Xiangchan Zhu,
-- "A Stochastic Analysis Approach to Lattice Yang--Mills at Strong Coupling",
-- Communications in Mathematical Physics 400 (2023), 805--851.
-- DOI: 10.1007/s00220-022-04609-1.
--
-- DASHI CONTRIBUTION
--
-- The RG effective action is quasi-local, not strictly finite-range.  Therefore
-- the correct finite-speed coordinate is an EXPONENTIALLY WEIGHTED influence
-- row, not exact sub-distance cancellation for the whole effective Hessian.
--
-- Step V already provides the rooted shell majorant
--
--     s_d <= (1/4) (1/2)^d.
--
-- If the unified derivative seminorm gives
--
--     h_d <= c_H s_d,
--
-- then with weight (3/2)^d,
--
--     (3/2)^d h_d
--       <= (c_H/4) (3/4)^d.
--
-- Since
--
--     (1/4) sum_{d>=0} (3/4)^d = 1,
--
-- every finite weighted Hessian-row partial sum is <= c_H, uniformly in
-- cutoff and volume.  This is exactly the quasi-local influence norm needed by
-- a weighted Gronwall/finite-speed argument.  No lattice-volume factor appears.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact as StepV
import DASHI.Physics.YangMills.BalabanRootedKPToHessianRowBudgetExact as Hess
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

threeHalves threeQuarters : ℚ
threeHalves = + 3 / 2
threeQuarters = + 3 / 4

threeHalvesPower threeQuartersPower : Nat → ℚ
threeHalvesPower zero = 1ℚ
threeHalvesPower (suc n) = threeHalvesPower n * threeHalves
threeQuartersPower zero = 1ℚ
threeQuartersPower (suc n) = threeQuartersPower n * threeQuarters

threeQuarterPartialSum : Nat → ℚ
threeQuarterPartialSum zero = 0ℚ
threeQuarterPartialSum (suc n) =
  threeQuarterPartialSum n + threeQuartersPower n

quarterThreeQuarterTailIdentity : ∀ n →
  StepV.quarter * threeQuarterPartialSum n + threeQuartersPower n ≡ 1ℚ
quarterThreeQuarterTailIdentity zero = refl
quarterThreeQuarterTailIdentity (suc n)
  rewrite quarterThreeQuarterTailIdentity n =
  ℚRing.solve []

quarterPartialBelowOne : ∀ n →
  StepV.quarter * threeQuarterPartialSum n ≤ 1ℚ
quarterPartialBelowOne n =
  let
    powerNonnegative : 0ℚ ≤ threeQuartersPower n
    powerNonnegative = powerNonnegativeProof n

    baseBelow :
      StepV.quarter * threeQuarterPartialSum n
      ≤ StepV.quarter * threeQuarterPartialSum n + threeQuartersPower n
    baseBelow = ℚP.≤-stepsʳ
      (StepV.quarter * threeQuarterPartialSum n)
      powerNonnegative
  in
  subst
    (λ upper → StepV.quarter * threeQuarterPartialSum n ≤ upper)
    (quarterThreeQuarterTailIdentity n)
    baseBelow
  where
  powerNonnegativeProof : ∀ depth → 0ℚ ≤ threeQuartersPower depth
  powerNonnegativeProof zero = ℚP.0≤1
  powerNonnegativeProof (suc depth) =
    Norm.productNonnegative
      (threeQuartersPower depth)
      threeQuarters
      (powerNonnegativeProof depth)
      threeQuartersNonnegative

  threeQuartersNonnegative : 0ℚ ≤ threeQuarters
  threeQuartersNonnegative =
    let
      instance
        qNonnegative : ℚ.NonNegative threeQuarters
        qNonnegative = ℚP.normalize-nonNeg 3 4
    in
    ℚP.nonNegative⁻¹ threeQuarters

halfThreeHalvesPowerIsThreeQuartersPower : ∀ n →
  threeHalvesPower n * StepV.halfPower n ≡ threeQuartersPower n
halfThreeHalvesPowerIsThreeQuartersPower zero = refl
halfThreeHalvesPowerIsThreeQuartersPower (suc n)
  rewrite halfThreeHalvesPowerIsThreeQuartersPower n =
  ℚRing.solve []

record ExponentialWeightedHessianShellControl
    (Scale Volume Root : Set) : Set₁ where
  field
    hessianControl : Hess.RootedHessianShellControl Scale Volume Root

open ExponentialWeightedHessianShellControl public

weightedHessianShell :
  ∀ {Scale Volume Root} →
  ExponentialWeightedHessianShellControl Scale Volume Root →
  Scale → Volume → Root → Nat → ℚ
weightedHessianShell dataSet scale volume root depth =
  threeHalvesPower depth
  * Hess.hessianRowShell (hessianControl dataSet) scale volume root depth

weightedHessianPartial :
  ∀ {Scale Volume Root} →
  ExponentialWeightedHessianShellControl Scale Volume Root →
  Scale → Volume → Root → Nat → ℚ
weightedHessianPartial dataSet scale volume root zero = 0ℚ
weightedHessianPartial dataSet scale volume root (suc depth) =
  weightedHessianPartial dataSet scale volume root depth
  + weightedHessianShell dataSet scale volume root depth

-- Pointwise shell estimate after inserting the 3/2 distance weight.
weightedShellBelowThreeQuarterMajorant :
  ∀ {Scale Volume Root}
    (dataSet : ExponentialWeightedHessianShellControl Scale Volume Root)
    scale volume root depth →
  weightedHessianShell dataSet scale volume root depth
  ≤ Hess.derivativeConstant (hessianControl dataSet)
      * StepV.quarter * threeQuartersPower depth
weightedShellBelowThreeQuarterMajorant dataSet scale volume root depth =
  let
    control = hessianControl dataSet

    first = Hess.hessianShellBelowActivityShell
      control scale volume root depth

    shell = StepV.rootedShellBelowMajorant
      (Hess.kpShell control) scale volume root depth

    derivativeScaled = Norm.scaleNonnegative
      (Hess.derivativeConstant control)
      (Hess.derivativeConstantNonnegative control)
      shell

    combined = ℚP.≤-trans first derivativeScaled

    weightNonnegative : 0ℚ ≤ threeHalvesPower depth
    weightNonnegative = weightPowerNonnegative depth

    weighted = Norm.scaleNonnegative
      (threeHalvesPower depth)
      weightNonnegative
      combined
  in
  subst
    (λ upper →
      weightedHessianShell dataSet scale volume root depth ≤ upper)
    (weightedMajorantIdentity
      (Hess.derivativeConstant control) depth)
    weighted
  where
  threeHalvesNonnegative : 0ℚ ≤ threeHalves
  threeHalvesNonnegative =
    let
      instance
        selected : ℚ.NonNegative threeHalves
        selected = ℚP.normalize-nonNeg 3 2
    in
    ℚP.nonNegative⁻¹ threeHalves

  weightPowerNonnegative : ∀ n → 0ℚ ≤ threeHalvesPower n
  weightPowerNonnegative zero = ℚP.0≤1
  weightPowerNonnegative (suc n) =
    Norm.productNonnegative
      (threeHalvesPower n)
      threeHalves
      (weightPowerNonnegative n)
      threeHalvesNonnegative

  weightedMajorantIdentity : ∀ derivative depth →
    threeHalvesPower depth
      * (derivative * (StepV.quarter * StepV.halfPower depth))
    ≡ derivative * StepV.quarter * threeQuartersPower depth
  weightedMajorantIdentity derivative depth
    rewrite halfThreeHalvesPowerIsThreeQuartersPower depth =
    ℚRing.solve []

weightedPartialBelowGeometricMajorant :
  ∀ {Scale Volume Root}
    (dataSet : ExponentialWeightedHessianShellControl Scale Volume Root)
    scale volume root depth →
  weightedHessianPartial dataSet scale volume root depth
  ≤ Hess.derivativeConstant (hessianControl dataSet)
      * StepV.quarter * threeQuarterPartialSum depth
weightedPartialBelowGeometricMajorant dataSet scale volume root zero =
  subst
    (λ right → 0ℚ ≤ right)
    (ℚRing.solve-∀ (Hess.derivativeConstant (hessianControl dataSet)))
    ℚP.≤-refl
weightedPartialBelowGeometricMajorant dataSet scale volume root (suc depth) =
  let
    previous = weightedPartialBelowGeometricMajorant
      dataSet scale volume root depth
    shell = weightedShellBelowThreeQuarterMajorant
      dataSet scale volume root depth
    added = ℚP.+-mono-≤ previous shell
  in
  subst
    (λ upper →
      weightedHessianPartial dataSet scale volume root (suc depth) ≤ upper)
    (ℚRing.solve-∀
      (Hess.derivativeConstant (hessianControl dataSet))
      (threeQuarterPartialSum depth)
      (threeQuartersPower depth))
    added

weightedHessianRowUniformlyBelowDerivativeConstant :
  ∀ {Scale Volume Root}
    (dataSet : ExponentialWeightedHessianShellControl Scale Volume Root)
    scale volume root depth →
  weightedHessianPartial dataSet scale volume root depth
  ≤ Hess.derivativeConstant (hessianControl dataSet)
weightedHessianRowUniformlyBelowDerivativeConstant dataSet scale volume root depth =
  let
    control = hessianControl dataSet
    first = weightedPartialBelowGeometricMajorant dataSet scale volume root depth
    partial = quarterPartialBelowOne depth
    scaled = Norm.scaleNonnegative
      (Hess.derivativeConstant control)
      (Hess.derivativeConstantNonnegative control)
      partial
  in
  ℚP.≤-trans first
    (subst
      (λ right →
        Hess.derivativeConstant control
          * StepV.quarter * threeQuarterPartialSum depth
        ≤ right)
      (ℚP.*-identityʳ (Hess.derivativeConstant control))
      scaled)

rootedKPToExponentiallyWeightedHessianLevel : ProofLevel
rootedKPToExponentiallyWeightedHessianLevel = machineChecked

-- Physical L7 seam is unchanged and now more valuable: prove the SAME
-- derivative seminorm shell comparison h_d <= c_H s_d.  Once supplied, it gives
-- both the unweighted c_H/2 Hessian row bound and this exponentially weighted
-- quasi-local row bound c_H.
physicalDerivativeSeminormControlsWeightedHessianLevel : ProofLevel
physicalDerivativeSeminormControlsWeightedHessianLevel = conditional
