module DASHI.Physics.YangMills.BalabanClayP2LargeFieldStepVExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational using
  ( ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _<_; _/_
  ; NonNegative; Positive; nonNegative )
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (baseBelowBasePlusRemainder)
open import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact using
  ( halfPower
  ; halfPowerNonnegative
  ; traceShellPartialSum
  ; traceShellGeometricIdentity
  )
open import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact

------------------------------------------------------------------------
-- P2A: exact gauge-invariant bad-block decomposition surface.
------------------------------------------------------------------------

record GaugeInvariantBadBlockDecomposition
    (Configuration GaugeTransform Block Polymer : Set) : Set₁ where
  field
    transform : GaugeTransform → Configuration → Configuration
    BadBlock : Configuration → Block → Set
    badPolymer : Configuration → Block → Polymer
    Contains : Polymer → Block → Set
    Connected : Polymer → Set

    badBlockGaugeInvariantForward : ∀ gauge configuration block →
      BadBlock configuration block →
      BadBlock (transform gauge configuration) block

    badBlockGaugeInvariantBackward : ∀ gauge configuration block →
      BadBlock (transform gauge configuration) block →
      BadBlock configuration block

    componentContainsSeed : ∀ configuration block →
      BadBlock configuration block →
      Contains (badPolymer configuration block) block

    componentConnected : ∀ configuration block →
      BadBlock configuration block →
      Connected (badPolymer configuration block)

    sameComponentUnique : ∀ configuration left right →
      BadBlock configuration left →
      BadBlock configuration right →
      Contains (badPolymer configuration left) right →
      badPolymer configuration left ≡ badPolymer configuration right

    maximalBadSetCovered : ∀ configuration block →
      BadBlock configuration block →
      Contains (badPolymer configuration block) block

    BadBlockMeasurable : Set
    CollarAssignmentConsistent : Set
    TransferRegionAssignmentConsistent : Set

    badBlockMeasurable : BadBlockMeasurable
    collarAssignmentConsistent : CollarAssignmentConsistent
    transferRegionAssignmentConsistent : TransferRegionAssignmentConsistent

open GaugeInvariantBadBlockDecomposition public

------------------------------------------------------------------------
-- P2C--P2F: explicit activity factorization and a common numerical margin.
------------------------------------------------------------------------

record LargeFieldActivityFactorization
    (Scale Polymer : Set) : Set₁ where
  field
    activityNorm : Scale → Polymer → ℚ
    polymerSize polymerDiameter : Scale → Polymer → ℚ

    actionFactor jacobianFactor determinantFactor bchFactor collarFactor
      chartSectorFactor : Scale → Polymer → ℚ

    multiply : ℚ → ℚ → ℚ

    activityBelowFactors : ∀ scale polymer →
      activityNorm scale polymer ≤
      multiply (actionFactor scale polymer)
        (multiply (jacobianFactor scale polymer)
          (multiply (determinantFactor scale polymer)
            (multiply (bchFactor scale polymer)
              (multiply (collarFactor scale polymer)
                (chartSectorFactor scale polymer)))))

    entropyExponent sizeSuppressionExponent diameterEntropyExponent
      diameterSuppressionExponent : ℚ

    sizeMargin : ℚ
    diameterMargin : ℚ

    sizeMarginExact :
      sizeMargin + entropyExponent ≡ sizeSuppressionExponent
    diameterMarginExact :
      diameterMargin + diameterEntropyExponent
      ≡ diameterSuppressionExponent

    SizeMarginPositive DiameterMarginPositive : Set
    sizeMarginPositive : SizeMarginPositive
    diameterMarginPositive : DiameterMarginPositive

    BlockingCompatible : Set
    TransferCutCompatible : Set
    NestedPatchCompatible : Set

    blockingCompatible : BlockingCompatible
    transferCutCompatible : TransferCutCompatible
    nestedPatchCompatible : NestedPatchCompatible

open LargeFieldActivityFactorization public

------------------------------------------------------------------------
-- P2G: a finite-volume KP theorem with an explicit eta = 1/2.
--
-- After entropy has been combined with activity suppression, assume the rooted
-- shell at depth n is at most (1/4) 2^{-n}.  The exact finite geometric identity
-- gives a volume-independent KP bound of 1/2, with a positive gap 1/2 to one.
------------------------------------------------------------------------

quarter half : ℚ
quarter = + 1 / 4
half = + 1 / 2

shellMajorant : Nat → ℚ
shellMajorant depth = quarter * halfPower depth

shellMajorantPartialSum : Nat → ℚ
shellMajorantPartialSum zero = 0ℚ
shellMajorantPartialSum (suc depth) =
  shellMajorantPartialSum depth + shellMajorant depth

shellMajorantPartialMatchesTrace : ∀ depth →
  shellMajorantPartialSum depth
  ≡ quarter * traceShellPartialSum depth
shellMajorantPartialMatchesTrace zero = ℚRing.solve-∀
shellMajorantPartialMatchesTrace (suc depth)
  rewrite shellMajorantPartialMatchesTrace depth =
  ℚRing.solve-∀ (traceShellPartialSum depth) (halfPower depth)

shellMajorantTailIdentity : ∀ depth →
  shellMajorantPartialSum depth + half * halfPower depth ≡ half
shellMajorantTailIdentity depth =
  trans
    (cong
      (λ partial → partial + half * halfPower depth)
      (shellMajorantPartialMatchesTrace depth))
    (trans
      (ℚRing.solve-∀
        (traceShellPartialSum depth) (halfPower depth))
      (cong (quarter *_) (traceShellGeometricIdentity depth)))

halfTimesPowerNonnegative : ∀ depth →
  0ℚ ≤ half * halfPower depth
halfTimesPowerNonnegative depth =
  let
    halfNonnegativeProof : 0ℚ ≤ half
    halfNonnegativeProof =
      let
        instance
          halfNonnegative : NonNegative half
          halfNonnegative = ℚP.normalize-nonNeg 1 2
      in
      ℚP.nonNegative⁻¹ half

    instance
      halfNonnegative : NonNegative half
      halfNonnegative = nonNegative halfNonnegativeProof

      powerNonnegative : NonNegative (halfPower depth)
      powerNonnegative = nonNegative (halfPowerNonnegative depth)

      productNonnegative : NonNegative (half * halfPower depth)
      productNonnegative = ℚP.nonNeg*nonNeg⇒nonNeg half (halfPower depth)
  in
  ℚP.nonNegative⁻¹ (half * halfPower depth)

shellMajorantPartialBelowHalf : ∀ depth →
  shellMajorantPartialSum depth ≤ half
shellMajorantPartialBelowHalf depth =
  subst
    (λ upper → shellMajorantPartialSum depth ≤ upper)
    (shellMajorantTailIdentity depth)
    (baseBelowBasePlusRemainder
      (shellMajorantPartialSum depth)
      (half * halfPower depth)
      (halfTimesPowerNonnegative depth))

record UniformRootedShellBound (Scale Volume Root : Set) : Set₁ where
  field
    rootedShell : Scale → Volume → Root → Nat → ℚ

    reflexive : ∀ value → value ≤ value
    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right
    addMonotone : ∀ {left leftUpper right rightUpper} →
      left ≤ leftUpper → right ≤ rightUpper →
      left + right ≤ leftUpper + rightUpper

    rootedShellBelowMajorant : ∀ scale volume root depth →
      rootedShell scale volume root depth ≤ shellMajorant depth

open UniformRootedShellBound public

rootedPartialSum :
  ∀ {Scale Volume Root} →
  UniformRootedShellBound Scale Volume Root →
  Scale → Volume → Root → Nat → ℚ
rootedPartialSum dataSet scale volume root zero = 0ℚ
rootedPartialSum dataSet scale volume root (suc depth) =
  rootedPartialSum dataSet scale volume root depth
  + rootedShell dataSet scale volume root depth

rootedPartialBelowMajorant :
  ∀ {Scale Volume Root}
    (dataSet : UniformRootedShellBound Scale Volume Root)
    scale volume root depth →
  rootedPartialSum dataSet scale volume root depth
  ≤ shellMajorantPartialSum depth
rootedPartialBelowMajorant dataSet scale volume root zero =
  reflexive dataSet 0ℚ
rootedPartialBelowMajorant dataSet scale volume root (suc depth) =
  addMonotone dataSet
    (rootedPartialBelowMajorant dataSet scale volume root depth)
    (rootedShellBelowMajorant dataSet scale volume root depth)

uniformFiniteVolumeKoteckyPreiss :
  ∀ {Scale Volume Root}
    (dataSet : UniformRootedShellBound Scale Volume Root)
    scale volume root depth →
  rootedPartialSum dataSet scale volume root depth ≤ half
uniformFiniteVolumeKoteckyPreiss dataSet scale volume root depth =
  transitive dataSet
    (rootedPartialBelowMajorant dataSet scale volume root depth)
    (shellMajorantPartialBelowHalf depth)

etaGapPositive : 0ℚ < half
etaGapPositive =
  let
    instance
      halfPositive : Positive half
      halfPositive = ℚP.normalize-pos 1 2
  in
  ℚP.positive⁻¹ half

etaPlusGapIsOne : half + half ≡ 1ℚ
etaPlusGapIsOne = ℚRing.solve-∀

------------------------------------------------------------------------
-- P2H: complete finite-volume Step V certificate.  Infinite-volume cluster
-- convergence and the concrete shell estimate are kept visible as producers.
------------------------------------------------------------------------

record PhysicalP2StepVCertificate
    (Configuration GaugeTransform Block Plaquette Polymer Scale Volume Root : Set)
    : Set₁ where
  field
    decomposition :
      GaugeInvariantBadBlockDecomposition
        Configuration GaugeTransform Block Polymer
    witnessGap : LargeFieldWitnessSystem Block Plaquette
    activityFactorization : LargeFieldActivityFactorization Scale Polymer
    shellBound : UniformRootedShellBound Scale Volume Root

    kpAtEveryFiniteCutoff : ∀ scale volume root depth →
      rootedPartialSum shellBound scale volume root depth ≤ half
    kpAtEveryFiniteCutoff = uniformFiniteVolumeKoteckyPreiss shellBound

    etaGap : 0ℚ < half
    etaGap = etaGapPositive

open PhysicalP2StepVCertificate public

p2GaugeInvariantSplitSurfaceLevel : ProofLevel
p2GaugeInvariantSplitSurfaceLevel = machineChecked

p2LocalWilsonActionGapLevel : ProofLevel
p2LocalWilsonActionGapLevel = machineChecked

p2FiniteVolumeKoteckyPreissLevel : ProofLevel
p2FiniteVolumeKoteckyPreissLevel = machineChecked

p2PhysicalBadBlockComponentProducerLevel : ProofLevel
p2PhysicalBadBlockComponentProducerLevel = conditional

p2PhysicalActivityShellProducerLevel : ProofLevel
p2PhysicalActivityShellProducerLevel = conditional

p2InfiniteClusterAndCorrelationProducerLevel : ProofLevel
p2InfiniteClusterAndCorrelationProducerLevel = conditional
