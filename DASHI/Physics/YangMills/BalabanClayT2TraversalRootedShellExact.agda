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
-- T2: the exact 8/16 mechanism.
--
-- A rooted trace has at most eight signed one-step extensions in four
-- dimensions.  If the total activity carried by each extension is at most
-- 1/16 of its parent shell, then one shell step costs at most 8/16 = 1/2.
-- Together with the root normalization 1/4 this produces exactly
--
--   rootedShell n <= (1/4) 2^{-n}.
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
    multiplyMonotoneLeft : ∀ prefix {left right} →
      left ≤ right → prefix * left ≤ prefix * right

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
        (multiplyMonotoneLeft dataSet eight
          (activityPerExtensionBelowOneSixteenth dataSet scale volume root depth))
        (reflexive dataSet
          ((eight * oneSixteenth)
            * rootedShell dataSet scale volume root depth))))

rootedShellBelowQuarterHalfPower :
  ∀ {Scale Volume Root}
    (dataSet : TraversalShellData Scale Volume Root)
    scale volume root depth →
  rootedShell dataSet scale volume root depth
  ≤ quarter * halfPower depth
rootedShellBelowQuarterHalfPower dataSet scale volume root zero =
  subst
    (λ upper → rootedShell dataSet scale volume root zero ≤ upper)
    (ℚRing.solve-∀)
    (rootNormalization dataSet scale volume root)
rootedShellBelowQuarterHalfPower dataSet scale volume root (suc depth) =
  subst
    (λ upper → rootedShell dataSet scale volume root (suc depth) ≤ upper)
    (ℚRing.solve-∀ (halfPower depth))
    (transitive dataSet
      (oneTraversalStepBelowHalf dataSet scale volume root depth)
      (multiplyMonotoneLeft dataSet half
        (rootedShellBelowQuarterHalfPower dataSet scale volume root depth)))

asUniformRootedShellBound :
  ∀ {Scale Volume Root} →
  TraversalShellData Scale Volume Root →
  P2.UniformRootedShellBound Scale Volume Root
asUniformRootedShellBound dataSet = record
  { P2.UniformRootedShellBound.rootedShell = rootedShell dataSet
  ; P2.UniformRootedShellBound.reflexive = reflexive dataSet
  ; P2.UniformRootedShellBound.transitive = transitive dataSet
  ; P2.UniformRootedShellBound.addMonotone = addMonotone dataSet
  ; P2.UniformRootedShellBound.rootedShellBelowMajorant =
      rootedShellBelowQuarterHalfPower dataSet
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

-- What remains physical is now sharply one statement: derive the 1/16 extension
-- activity from the Wilson action, Haar Jacobian, determinant, BCH, localization,
-- entropy collars and transfer geometry in the common analytic norm.
wilsonActivityPerTraversalBelowOneSixteenthLevel : ProofLevel
wilsonActivityPerTraversalBelowOneSixteenthLevel = conditional
