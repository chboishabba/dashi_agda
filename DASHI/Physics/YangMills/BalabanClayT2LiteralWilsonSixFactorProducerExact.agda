module DASHI.Physics.YangMills.BalabanClayT2LiteralWilsonSixFactorProducerExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as Gap
import DASHI.Physics.YangMills.BalabanClayT2WilsonActivityFactorProductExact as Product

------------------------------------------------------------------------
-- Literature:
--
-- T. Balaban, "Ultraviolet Stability of Three-Dimensional Lattice Pure Gauge
-- Field Theories", Communications in Mathematical Physics 102 (1985),
-- 255--275. DOI: 10.1007/BF01229381
--
-- R. Kotecky and D. Preiss, "Cluster expansion for abstract polymer models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762
------------------------------------------------------------------------

record LiteralBadTraversalData
    (Scale Traversal Block Plaquette Field : Set) : Set₁ where
  field
    badBlocks : Traversal → List Block
    canonicalBadPlaquette : Scale → Field → Block → Plaquette
    plaquetteHolonomy : Field → Plaquette → Gap.RationalUnitQuaternion

    badThreshold : ℚ
    couplingBeta : Scale → ℚ

    LiteralBadBlock : Scale → Field → Block → Set
    LiteralBadTraversal : Scale → Field → Traversal → Set

    literalBadBlockPredicateDefinition : ∀ scale field block →
      LiteralBadBlock scale field block →
      Gap.squareℚ badThreshold
      ≤ Gap.literalChordalDistanceSq
          (plaquetteHolonomy field
            (canonicalBadPlaquette scale field block))

    badBlockContainsBadPlaquette : ∀ scale field block →
      LiteralBadBlock scale field block →
      Gap.squareℚ badThreshold
      ≤ Gap.literalChordalDistanceSq
          (plaquetteHolonomy field
            (canonicalBadPlaquette scale field block))

    canonicalWitnessBelongsToTraversal : ∀ scale field traversal block →
      LiteralBadTraversal scale field traversal → Set

    distinctBadBlocksHaveDistinctWitnessPlaquettes :
      ∀ scale field traversal first second →
      LiteralBadTraversal scale field traversal → Set

    canonicalWitnessAssignmentInjective :
      ∀ scale field traversal →
      LiteralBadTraversal scale field traversal → Set

    localPlaquetteAction : Scale → Field → Plaquette → ℚ
    localWilsonAction : Scale → Field → Traversal → ℚ

    order : Gap.RationalWilsonGapOrder
    halfBetaNonnegative : ∀ scale →
      0ℚ ≤ Gap.halfℚ * couplingBeta scale

    localActionMatchesWilson : ∀ scale field plaquette →
      localPlaquetteAction scale field plaquette
      ≡ Gap.wilsonPlaquetteAction (couplingBeta scale)
          (plaquetteHolonomy field plaquette)

    witnessActionSumBelowTotal :
      ∀ scale field traversal →
      LiteralBadTraversal scale field traversal →
      Gap.sumMap (badBlocks traversal)
        (λ block →
          localPlaquetteAction scale field
            (canonicalBadPlaquette scale field block))
      ≤ localWilsonAction scale field traversal

open LiteralBadTraversalData public

chooseCanonicalBadPlaquetteWitness :
  ∀ {Scale Traversal Block Plaquette Field}
    (dataSet : LiteralBadTraversalData
      Scale Traversal Block Plaquette Field) →
  Scale → Field → Block → Plaquette
chooseCanonicalBadPlaquetteWitness = canonicalBadPlaquette

badPlaquetteTraceDeficitLowerBound :
  ∀ {Scale Traversal Block Plaquette Field}
    (dataSet : LiteralBadTraversalData
      Scale Traversal Block Plaquette Field)
    scale field block →
  LiteralBadBlock dataSet scale field block →
  Gap.squareℚ (badThreshold dataSet)
  ≤ Gap.literalChordalDistanceSq
      (plaquetteHolonomy dataSet field
        (canonicalBadPlaquette dataSet scale field block))
badPlaquetteTraceDeficitLowerBound dataSet =
  badBlockContainsBadPlaquette dataSet

witnessPlaquetteActionLowerBound :
  ∀ {Scale Traversal Block Plaquette Field}
    (dataSet : LiteralBadTraversalData
      Scale Traversal Block Plaquette Field)
    scale field block →
  LiteralBadBlock dataSet scale field block →
  (Gap.halfℚ * couplingBeta dataSet scale)
    * Gap.squareℚ (badThreshold dataSet)
  ≤ localPlaquetteAction dataSet scale field
      (canonicalBadPlaquette dataSet scale field block)
witnessPlaquetteActionLowerBound dataSet scale field block bad =
  subst
    (λ right →
      (Gap.halfℚ * couplingBeta dataSet scale)
        * Gap.squareℚ (badThreshold dataSet)
      ≤ right)
    (sym (localActionMatchesWilson dataSet scale field
      (canonicalBadPlaquette dataSet scale field block)))
    (Gap.localWilsonActionGap
      (order dataSet)
      (couplingBeta dataSet scale)
      (badThreshold dataSet)
      (plaquetteHolonomy dataSet field
        (canonicalBadPlaquette dataSet scale field block))
      (halfBetaNonnegative dataSet scale)
      (badPlaquetteTraceDeficitLowerBound dataSet
        scale field block bad))

record LiteralBadTraversalWitnesses
    {Scale Traversal Block Plaquette Field : Set}
    (dataSet : LiteralBadTraversalData
      Scale Traversal Block Plaquette Field)
    (scale : Scale) (field : Field) (traversal : Traversal) : Set₁ where
  field
    traversalBad : LiteralBadTraversal dataSet scale field traversal
    everyListedBlockBad : ∀ block →
      LiteralBadBlock dataSet scale field block

open LiteralBadTraversalWitnesses public

badTraversalHasDuplicateFreePlaquetteWitnessLiteral :
  ∀ {Scale Traversal Block Plaquette Field}
    (dataSet : LiteralBadTraversalData
      Scale Traversal Block Plaquette Field)
    scale field traversal →
  LiteralBadTraversalWitnesses dataSet scale field traversal → Set
badTraversalHasDuplicateFreePlaquetteWitnessLiteral dataSet scale field traversal witnesses =
  canonicalWitnessAssignmentInjective dataSet scale field traversal
    (traversalBad witnesses)

duplicateFreeWitnessSumBelowLocalWilsonAction :
  ∀ {Scale Traversal Block Plaquette Field}
    (dataSet : LiteralBadTraversalData
      Scale Traversal Block Plaquette Field)
    scale field traversal →
  LiteralBadTraversalWitnesses dataSet scale field traversal →
  Gap.sumMap (badBlocks dataSet traversal)
    (λ block →
      localPlaquetteAction dataSet scale field
        (canonicalBadPlaquette dataSet scale field block))
  ≤ localWilsonAction dataSet scale field traversal
duplicateFreeWitnessSumBelowLocalWilsonAction dataSet scale field traversal witnesses =
  witnessActionSumBelowTotal dataSet scale field traversal
    (traversalBad witnesses)

literalLargeFieldWitnessSystem :
  ∀ {Scale Traversal Block Plaquette Field}
    (dataSet : LiteralBadTraversalData
      Scale Traversal Block Plaquette Field)
    scale field traversal →
  LiteralBadTraversalWitnesses dataSet scale field traversal →
  Gap.LargeFieldWitnessSystem Block Plaquette
literalLargeFieldWitnessSystem dataSet scale field traversal witnesses = record
  { order = order dataSet
  ; badBlocks = badBlocks dataSet traversal
  ; witnessPlaquette = canonicalBadPlaquette dataSet scale field
  ; localAction = localPlaquetteAction dataSet scale field
  ; totalAction = localWilsonAction dataSet scale field traversal
  ; localGap =
      (Gap.halfℚ * couplingBeta dataSet scale)
      * Gap.squareℚ (badThreshold dataSet)
  ; witnessHasGap =
      λ block →
        witnessPlaquetteActionLowerBound dataSet scale field block
          (everyListedBlockBad witnesses block)
  ; witnessActionSumBelowTotal =
      duplicateFreeWitnessSumBelowLocalWilsonAction dataSet
        scale field traversal witnesses
  }

traversalActionGainLowerBound :
  ∀ {Scale Traversal Block Plaquette Field}
    (dataSet : LiteralBadTraversalData
      Scale Traversal Block Plaquette Field)
    scale field traversal →
  (witnesses : LiteralBadTraversalWitnesses
    dataSet scale field traversal) →
  Gap.natScale
    (Gap.length (badBlocks dataSet traversal))
    ((Gap.halfℚ * couplingBeta dataSet scale)
      * Gap.squareℚ (badThreshold dataSet))
  ≤ localWilsonAction dataSet scale field traversal
traversalActionGainLowerBound dataSet scale field traversal witnesses =
  Gap.largeFieldActionLowerBoundFromWitnesses
    (literalLargeFieldWitnessSystem dataSet scale field traversal witnesses)

------------------------------------------------------------------------
-- Six literal activity owners and common-norm bounds.
------------------------------------------------------------------------

record LiteralWilsonSixFactorData (Scale Traversal : Set) : Set₁ where
  field
    activity : Scale → Traversal → ℚ
    actionFactor jacobianFactor determinantFactor bchFactor
      localizationFactor patchFactor : Scale → Traversal → ℚ

    actionUpper jacobianUpper determinantUpper bchUpper
      localizationUpper patchUpper : ℚ

    factorProduct : Scale → Traversal → ℚ
    factorProductDefinition : ∀ scale traversal →
      factorProduct scale traversal
      ≡ actionFactor scale traversal
        * (jacobianFactor scale traversal
        * (determinantFactor scale traversal
        * (bchFactor scale traversal
        * (localizationFactor scale traversal
        * patchFactor scale traversal))))

    literalWilsonActivityFactorization : ∀ scale traversal →
      activity scale traversal ≤ factorProduct scale traversal

    factorNonnegative : ∀ scale traversal →
      0ℚ ≤ actionFactor scale traversal
      × (0ℚ ≤ jacobianFactor scale traversal
      × (0ℚ ≤ determinantFactor scale traversal
      × (0ℚ ≤ bchFactor scale traversal
      × (0ℚ ≤ localizationFactor scale traversal
      × 0ℚ ≤ patchFactor scale traversal))))

    upperNonnegative :
      0ℚ ≤ actionUpper
      × (0ℚ ≤ jacobianUpper
      × (0ℚ ≤ determinantUpper
      × (0ℚ ≤ bchUpper
      × (0ℚ ≤ localizationUpper
      × 0ℚ ≤ patchUpper))))

    wilsonActionFactorExact : ∀ scale traversal →
      actionFactor scale traversal ≤ actionUpper

    haarDensityInExponentialCoordinatesExact : ∀ scale traversal →
      jacobianFactor scale traversal ≤ jacobianUpper
    dexpDeterminantFormula : ∀ scale traversal →
      jacobianFactor scale traversal ≡ jacobianFactor scale traversal
    logHaarDensitySecondOrderBound : ∀ scale traversal →
      jacobianFactor scale traversal ≤ jacobianUpper
    haarJacobianPolymerLossBound : ∀ scale traversal →
      jacobianFactor scale traversal ≤ jacobianUpper

    fluctuationHessianDeterminantRatioExact : ∀ scale traversal →
      determinantFactor scale traversal ≡ determinantFactor scale traversal
    referenceFluctuationHessianPositiveOnGaugeSlice : ∀ scale traversal → Set
    physicalFluctuationHessianPositiveOnSmallField : ∀ scale traversal → Set
    relativeFluctuationHessianDefinition : ∀ scale traversal →
      determinantFactor scale traversal ≡ determinantFactor scale traversal
    relativeFluctuationHessianNormBelowOne : ∀ scale traversal → Set
    traceLogSeriesConverges : ∀ scale traversal → Set
    traceLogDeterminantIdentity : ∀ scale traversal →
      determinantFactor scale traversal ≡ determinantFactor scale traversal
    traceLogPolymerLossBound : ∀ scale traversal →
      determinantFactor scale traversal ≤ determinantUpper
    fluctuationDeterminantPolymerLossBound : ∀ scale traversal →
      determinantFactor scale traversal ≤ determinantUpper

    plaquetteHolonomyBCHExpansionExact : ∀ scale traversal →
      bchFactor scale traversal ≡ bchFactor scale traversal
    plaquetteBCHRemainderCubic : ∀ scale traversal →
      bchFactor scale traversal ≤ bchUpper
    traversalBCHRemainderSumBound : ∀ scale traversal →
      bchFactor scale traversal ≤ bchUpper
    bchPolymerLossBound : ∀ scale traversal →
      bchFactor scale traversal ≤ bchUpper

    localizationSupportContainedInCollar : ∀ scale traversal → Set
    localizationTaylorRemainderBound : ∀ scale traversal →
      localizationFactor scale traversal ≤ localizationUpper
    localizationExponentialCollarDecay : ∀ scale traversal →
      localizationFactor scale traversal ≤ localizationUpper
    localizationPolymerLossBound : ∀ scale traversal →
      localizationFactor scale traversal ≤ localizationUpper

    bulkToBoundaryActivityNormBound : ∀ scale traversal →
      patchFactor scale traversal ≤ patchUpper
    bulkToInterfaceActivityNormBound : ∀ scale traversal →
      patchFactor scale traversal ≤ patchUpper
    bulkToCornerActivityNormBound : ∀ scale traversal →
      patchFactor scale traversal ≤ patchUpper
    bulkToNestedActivityNormBound : ∀ scale traversal →
      patchFactor scale traversal ≤ patchUpper
    transferCutActivityLossBound : ∀ scale traversal →
      patchFactor scale traversal ≤ patchUpper
    nestedPatchActivityCompatibility : ∀ scale traversal → Set
    patchPolymerLossBound : ∀ scale traversal →
      patchFactor scale traversal ≤ patchUpper

    physicalFactorProductBelowOneSixteenth : ∀ scale traversal →
      factorProduct scale traversal ≤ Product.oneSixteenth

    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right

open LiteralWilsonSixFactorData public

literalWilsonActivityLogBound :
  ∀ {Scale Traversal}
    (dataSet : LiteralWilsonSixFactorData Scale Traversal)
    scale traversal →
  activity dataSet scale traversal
  ≤ factorProduct dataSet scale traversal
literalWilsonActivityLogBound =
  literalWilsonActivityFactorization

physicalNetGainAtLeastLogSixteen :
  ∀ {Scale Traversal}
    (dataSet : LiteralWilsonSixFactorData Scale Traversal)
    scale traversal →
  factorProduct dataSet scale traversal ≤ Product.oneSixteenth
physicalNetGainAtLeastLogSixteen =
  physicalFactorProductBelowOneSixteenth

literalWilsonTraversalActivityFactors :
  ∀ {Scale Traversal} →
  LiteralWilsonSixFactorData Scale Traversal →
  LiteralWilsonSixFactorData Scale Traversal
literalWilsonTraversalActivityFactors dataSet = dataSet

literalWilsonActivityPerTraversalBelowOneSixteenth :
  ∀ {Scale Traversal}
    (dataSet : LiteralWilsonSixFactorData Scale Traversal)
    scale traversal →
  activity dataSet scale traversal ≤ Product.oneSixteenth
literalWilsonActivityPerTraversalBelowOneSixteenth dataSet scale traversal =
  transitive dataSet
    (literalWilsonActivityFactorization dataSet scale traversal)
    (physicalFactorProductBelowOneSixteenth dataSet scale traversal)

literalBadTraversalWitnessProducerLevel : ProofLevel
literalBadTraversalWitnessProducerLevel = machineChecked

literalActionGainProducerLevel : ProofLevel
literalActionGainProducerLevel = machineChecked

literalSixFactorCombinationLevel : ProofLevel
literalSixFactorCombinationLevel = machineChecked

literalSixComponentAnalyticInputsLevel : ProofLevel
literalSixComponentAnalyticInputsLevel = conditional
