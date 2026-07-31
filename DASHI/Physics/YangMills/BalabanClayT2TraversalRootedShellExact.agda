module DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact
  using (half; halfPower)
import DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact as P2

------------------------------------------------------------------------
-- T2: the exact 8/16 Kotecký--Preiss specialisation.
--
-- R. Kotecký and D. Preiss,
-- "Cluster expansion for abstract polymer models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762
--
-- This module certifies the conservative KP lane.  The distinct Dobrushin,
-- Fernández--Procacci and extended Gruber--Kunz lanes, together with the valid
-- implication directions between their neighbourhood majorants, are formalized
-- in BalabanClayT2ClusterCriterionComparisonExact.
--
-- A rooted trace has at most eight signed one-step extensions in four
-- dimensions.  If the absolute activity carried by each extension is at most
-- 1/16 of its parent shell, then one shell step costs at most 8/16 = 1/2.
-- Together with the root normalization 1/4 this produces exactly
--
--   rootedShell n <= (1/4) 2^{-n}.
--
-- Order discipline: monotonicity is required only for multiplication by the
-- two fixed positive constants 8 and 1/2.  No false arbitrary-rational
-- multiplication law is admitted.
------------------------------------------------------------------------

eight oneSixteenth quarter : ℚ
eight = + 8 / 1
oneSixteenth = + 1 / 16
quarter = + 1 / 4

eightTimesOneSixteenthIsHalf :
  eight * oneSixteenth ≡ half
eightTimesOneSixteenthIsHalf = ℚRing.solve-∀

record TraversalShellData (Scale Volume Root : Set) : Set₁ where
  field
    rootedShell extensionActivity : Scale → Volume → Root → Nat → ℚ

    reflexive : ∀ value → value ≤ value
    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      left ≤ leftUpper → right ≤ rightUpper →
      left + right ≤ leftUpper + rightUpper

    multiplyByEightMonotone : ∀ {left right} →
      left ≤ right → eight * left ≤ eight * right
    multiplyByHalfMonotone : ∀ {left right} →
      left ≤ right → half * left ≤ half * right

    rootNormalization : ∀ scale volume root →
      rootedShell scale volume root zero ≤ quarter

    atMostEightExtensions : ∀ scale volume root depth →
      rootedShell scale volume root (suc depth)
      ≤ eight * extensionActivity scale volume root depth

    activityPerExtensionBelowOneSixteenth : ∀ scale volume root depth →
      extensionActivity scale volume root depth
      ≤ oneSixteenth * rootedShell scale volume root depth

open TraversalShellData public

oneTraversalStepBelowHalf :
  ∀ {Scale Volume Root}
    (dataSet : TraversalShellData Scale Volume Root)
    scale volume root depth →
  rootedShell dataSet scale volume root (suc depth)
  ≤ half * rootedShell dataSet scale volume root depth
oneTraversalStepBelowHalf dataSet scale volume root depth =
  subst
    (λ coefficient →
      rootedShell dataSet scale volume root (suc depth)
      ≤ coefficient * rootedShell dataSet scale volume root depth)
    eightTimesOneSixteenthIsHalf
    (transitive dataSet
      (atMostEightExtensions dataSet scale volume root depth)
      (transitive dataSet
        (multiplyByEightMonotone dataSet
          (activityPerExtensionBelowOneSixteenth dataSet scale volume root depth))
        (subst
          (λ upper →
            eight * (oneSixteenth
              * rootedShell dataSet scale volume root depth)
            ≤ upper)
          (regroupEightOneSixteenth (rootedShell dataSet scale volume root depth))
          (reflexive dataSet
            (eight * (oneSixteenth
              * rootedShell dataSet scale volume root depth))))))
  where
  regroupEightOneSixteenth : ∀ (x : ℚ) → eight * (oneSixteenth * x) ≡ half * x
  regroupEightOneSixteenth = ℚRing.solve-∀

rootedShellBelowQuarterHalfPower :
  ∀ {Scale Volume Root}
    (dataSet : TraversalShellData Scale Volume Root)
    scale volume root depth →
  rootedShell dataSet scale volume root depth
  ≤ quarter * halfPower depth
rootedShellBelowQuarterHalfPower dataSet scale volume root zero =
  subst
    (λ upper → rootedShell dataSet scale volume root zero ≤ upper)
    regroupQuarter
    (rootNormalization dataSet scale volume root)
  where
  regroupQuarter : quarter ≡ quarter * halfPower zero
  regroupQuarter = ℚRing.solve-∀
rootedShellBelowQuarterHalfPower dataSet scale volume root (suc depth) =
  subst
    (λ upper → rootedShell dataSet scale volume root (suc depth) ≤ upper)
    (regroupHalf (halfPower depth))
    (transitive dataSet
      (oneTraversalStepBelowHalf dataSet scale volume root depth)
      (multiplyByHalfMonotone dataSet
        (rootedShellBelowQuarterHalfPower dataSet scale volume root depth)))
  where
  regroupHalf : ∀ h → half * (quarter * h) ≡ quarter * (half * h)
  regroupHalf = ℚRing.solve-∀

asUniformRootedShellBound :
  ∀ {Scale Volume Root} →
  TraversalShellData Scale Volume Root →
  P2.UniformRootedShellBound Scale Volume Root
asUniformRootedShellBound dataSet = record
  { rootedShell = rootedShell dataSet
  ; reflexive = reflexive dataSet
  ; transitive = transitive dataSet
  ; addMonotone = addMonotone dataSet
  ; rootedShellBelowMajorant = rootedShellBelowQuarterHalfPower dataSet
  }

traversalSuppressionImpliesFiniteKP :
  ∀ {Scale Volume Root}
    (dataSet : TraversalShellData Scale Volume Root)
    scale volume root depth →
  P2.rootedPartialSum (asUniformRootedShellBound dataSet)
    scale volume root depth
  ≤ P2.half
traversalSuppressionImpliesFiniteKP dataSet =
  P2.uniformFiniteVolumeKoteckyPreiss (asUniformRootedShellBound dataSet)

traversalEightOverSixteenLevel : ProofLevel
traversalEightOverSixteenLevel = machineChecked

rootedShellQuarterHalfPowerLevel : ProofLevel
rootedShellQuarterHalfPowerLevel = machineChecked

rootedShellToFiniteKoteckyPreissLevel : ProofLevel
rootedShellToFiniteKoteckyPreissLevel = machineChecked

rootedTraversalCriterionIsKPLevel : ProofLevel
rootedTraversalCriterionIsKPLevel = machineChecked

rootedShellPositiveMultiplierDisciplineLevel : ProofLevel
rootedShellPositiveMultiplierDisciplineLevel = machineChecked

-- What remains physical is now sharply one statement: derive the 1/16 extension
-- activity from the Wilson action, Haar Jacobian, determinant, BCH, localization,
-- entropy collars and transfer geometry in the common analytic norm.
wilsonActivityPerTraversalBelowOneSixteenthLevel : ProofLevel
wilsonActivityPerTraversalBelowOneSixteenthLevel = conditional
