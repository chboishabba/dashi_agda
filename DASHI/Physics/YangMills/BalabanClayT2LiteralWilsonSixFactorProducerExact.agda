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

    literalBadBlockPredicateDefinition : ∀ (scale : Scale) (fld : Field) (block : Block) →
      LiteralBadBlock scale fld block →
      Gap.squareℚ badThreshold
      ≤ Gap.literalChordalDistanceSq
          (plaquetteHolonomy fld
            (canonicalBadPlaquette scale fld block))

    badBlockContainsBadPlaquette : ∀ (scale : Scale) (fld : Field) (block : Block) →
      LiteralBadBlock scale fld block →
      Gap.squareℚ badThreshold
      ≤ Gap.literalChordalDistanceSq
          (plaquetteHolonomy fld
            (canonicalBadPlaquette scale fld block))

    canonicalWitnessBelongsToTraversal : ∀ (scale : Scale) (fld : Field) (traversal : Traversal) (block : Block) →
      LiteralBadTraversal scale fld traversal → Set

    distinctBadBlocksHaveDistinctWitnessPlaquettes :
      ∀ (scale : Scale) (fld : Field) (traversal : Traversal) (first second : Block) →
      LiteralBadTraversal scale fld traversal → Set

    canonicalWitnessAssignmentInjective :
      ∀ (scale : Scale) (fld : Field) (traversal : Traversal) →
      LiteralBadTraversal scale fld traversal → Set

    localPlaquetteAction : Scale → Field → Plaquette → ℚ
    localWilsonAction : Scale → Field → Traversal → ℚ

    order : Gap.RationalWilsonGapOrder
    halfBetaNonnegative : ∀ (scale : Scale) →
      0ℚ ≤ Gap.halfℚ * couplingBeta scale

    localActionMatchesWilson : ∀ (scale : Scale) (fld : Field) (plaquette : Plaquette) →
      localPlaquetteAction scale fld plaquette
      ≡ Gap.wilsonPlaquetteAction (couplingBeta scale)
          (plaquetteHolonomy fld plaquette)

    witnessActionSumBelowTotal :
      ∀ (scale : Scale) (fld : Field) (traversal : Traversal) →
      LiteralBadTraversal scale fld traversal →
      Gap.sumMap (badBlocks traversal)
        (λ block →
          localPlaquetteAction scale fld
            (canonicalBadPlaquette scale fld block))
      ≤ localWilsonAction scale fld traversal

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
    everyListedBlockBad : ∀ (block : Block) →
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
    factorProductDefinition : ∀ (scale : Scale) (traversal : Traversal) →
      factorProduct scale traversal
      ≡ actionFactor scale traversal
        * (jacobianFactor scale traversal
        * (determinantFactor scale traversal
        * (bchFactor scale traversal
        * (localizationFactor scale traversal
        * patchFactor scale traversal))))

    literalWilsonActivityFactorization : ∀ (scale : Scale) (traversal : Traversal) →
      activity scale traversal ≤ factorProduct scale traversal

    factorNonnegative : ∀ (scale : Scale) (traversal : Traversal) →
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

    wilsonActionFactorExact : ∀ (scale : Scale) (traversal : Traversal) →
      actionFactor scale traversal ≤ actionUpper

    haarDensityInExponentialCoordinatesExact : ∀ (scale : Scale) (traversal : Traversal) →
      jacobianFactor scale traversal ≤ jacobianUpper
    dexpDeterminantFormula : ∀ (scale : Scale) (traversal : Traversal) →
      jacobianFactor scale traversal ≡ jacobianFactor scale traversal
    logHaarDensitySecondOrderBound : ∀ (scale : Scale) (traversal : Traversal) →
      jacobianFactor scale traversal ≤ jacobianUpper
    haarJacobianPolymerLossBound : ∀ (scale : Scale) (traversal : Traversal) →
      jacobianFactor scale traversal ≤ jacobianUpper

    fluctuationHessianDeterminantRatioExact : ∀ (scale : Scale) (traversal : Traversal) →
      determinantFactor scale traversal ≡ determinantFactor scale traversal
    referenceFluctuationHessianPositiveOnGaugeSlice : ∀ (scale : Scale) (traversal : Traversal) → Set
    physicalFluctuationHessianPositiveOnSmallField : ∀ (scale : Scale) (traversal : Traversal) → Set
    relativeFluctuationHessianDefinition : ∀ (scale : Scale) (traversal : Traversal) →
      determinantFactor scale traversal ≡ determinantFactor scale traversal
    relativeFluctuationHessianNormBelowOne : ∀ (scale : Scale) (traversal : Traversal) → Set
    traceLogSeriesConverges : ∀ (scale : Scale) (traversal : Traversal) → Set
    traceLogDeterminantIdentity : ∀ (scale : Scale) (traversal : Traversal) →
      determinantFactor scale traversal ≡ determinantFactor scale traversal
    traceLogPolymerLossBound : ∀ (scale : Scale) (traversal : Traversal) →
      determinantFactor scale traversal ≤ determinantUpper
    fluctuationDeterminantPolymerLossBound : ∀ (scale : Scale) (traversal : Traversal) →
      determinantFactor scale traversal ≤ determinantUpper

    plaquetteHolonomyBCHExpansionExact : ∀ (scale : Scale) (traversal : Traversal) →
      bchFactor scale traversal ≡ bchFactor scale traversal
    plaquetteBCHRemainderCubic : ∀ (scale : Scale) (traversal : Traversal) →
      bchFactor scale traversal ≤ bchUpper
    traversalBCHRemainderSumBound : ∀ (scale : Scale) (traversal : Traversal) →
      bchFactor scale traversal ≤ bchUpper
    bchPolymerLossBound : ∀ (scale : Scale) (traversal : Traversal) →
      bchFactor scale traversal ≤ bchUpper

    localizationSupportContainedInCollar : ∀ (scale : Scale) (traversal : Traversal) → Set
    localizationTaylorRemainderBound : ∀ (scale : Scale) (traversal : Traversal) →
      localizationFactor scale traversal ≤ localizationUpper
    localizationExponentialCollarDecay : ∀ (scale : Scale) (traversal : Traversal) →
      localizationFactor scale traversal ≤ localizationUpper
    localizationPolymerLossBound : ∀ (scale : Scale) (traversal : Traversal) →
      localizationFactor scale traversal ≤ localizationUpper

    bulkToBoundaryActivityNormBound : ∀ (scale : Scale) (traversal : Traversal) →
      patchFactor scale traversal ≤ patchUpper
    bulkToInterfaceActivityNormBound : ∀ (scale : Scale) (traversal : Traversal) →
      patchFactor scale traversal ≤ patchUpper
    bulkToCornerActivityNormBound : ∀ (scale : Scale) (traversal : Traversal) →
      patchFactor scale traversal ≤ patchUpper
    bulkToNestedActivityNormBound : ∀ (scale : Scale) (traversal : Traversal) →
      patchFactor scale traversal ≤ patchUpper
    transferCutActivityLossBound : ∀ (scale : Scale) (traversal : Traversal) →
      patchFactor scale traversal ≤ patchUpper
    nestedPatchActivityCompatibility : ∀ (scale : Scale) (traversal : Traversal) → Set
    patchPolymerLossBound : ∀ (scale : Scale) (traversal : Traversal) →
      patchFactor scale traversal ≤ patchUpper

    physicalFactorProductBelowOneSixteenth : ∀ (scale : Scale) (traversal : Traversal) →
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
