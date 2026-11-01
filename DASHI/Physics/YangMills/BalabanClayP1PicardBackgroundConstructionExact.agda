module DASHI.Physics.YangMills.BalabanClayP1PicardBackgroundConstructionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP1BackgroundStabilityExact as P1

------------------------------------------------------------------------
-- Constructive Picard production of the nonlinear background.
--
-- The background is never supplied as a field.  It is definitionally the limit
-- of the recursively generated critical-map orbit.  Completeness enters through
-- the limit laws; fixedness and uniqueness are proved from those laws and the
-- strict contraction estimate.
------------------------------------------------------------------------

record PicardCoreData (Coarse State Bound : Set) : Set₁ where
  field
    criticalMap : Coarse → State → State
    seed : Coarse → State

    limit : (Nat → State) → State
    limitCongruent : ∀ {left right : Nat → State} →
      (∀ depth → left depth ≡ right depth) → limit left ≡ limit right
    mapCommutesWithLimit : ∀ coarse sequence →
      criticalMap coarse (limit sequence)
      ≡ limit (λ depth → criticalMap coarse (sequence depth))
    tailShiftPreservesLimit : ∀ sequence →
      limit (λ depth → sequence (suc depth)) ≡ limit sequence

    distance : State → State → Bound
    rho : Bound
    scale : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    contractive : ∀ coarse left right →
      LessEqual
        (distance (criticalMap coarse left) (criticalMap coarse right))
        (scale rho (distance left right))

    strictShrinkForcesEquality : ∀ left right →
      LessEqual (distance left right) (scale rho (distance left right)) →
      left ≡ right

open PicardCoreData public

picard :
  ∀ {Coarse State Bound} →
  PicardCoreData Coarse State Bound → Coarse → Nat → State
picard dataSet coarse zero = seed dataSet coarse
picard dataSet coarse (suc depth) =
  criticalMap dataSet coarse (picard dataSet coarse depth)

picardStep :
  ∀ {Coarse State Bound}
    (dataSet : PicardCoreData Coarse State Bound)
    coarse depth →
  criticalMap dataSet coarse (picard dataSet coarse depth)
  ≡ picard dataSet coarse (suc depth)
picardStep dataSet coarse depth = refl

picardBackgroundCore :
  ∀ {Coarse State Bound} →
  PicardCoreData Coarse State Bound → Coarse → State
picardBackgroundCore dataSet coarse =
  limit dataSet (picard dataSet coarse)

picardBackgroundCoreFixed :
  ∀ {Coarse State Bound}
    (dataSet : PicardCoreData Coarse State Bound)
    coarse →
  criticalMap dataSet coarse (picardBackgroundCore dataSet coarse)
  ≡ picardBackgroundCore dataSet coarse
picardBackgroundCoreFixed dataSet coarse =
  trans
    (mapCommutesWithLimit dataSet coarse (picard dataSet coarse))
    (trans
      (limitCongruent dataSet (λ depth → picardStep dataSet coarse depth))
      (tailShiftPreservesLimit dataSet (picard dataSet coarse)))

fixedPointUniqueCore :
  ∀ {Coarse State Bound}
    (dataSet : PicardCoreData Coarse State Bound)
    coarse left right →
  criticalMap dataSet coarse left ≡ left →
  criticalMap dataSet coarse right ≡ right →
  left ≡ right
fixedPointUniqueCore dataSet coarse left right leftFixed rightFixed =
  strictShrinkForcesEquality dataSet left right
    (subst
      (λ value → LessEqual dataSet value
        (scale dataSet (rho dataSet) (distance dataSet left right)))
      (cong₂ (distance dataSet) leftFixed rightFixed)
      (contractive dataSet coarse left right))

------------------------------------------------------------------------
-- Wilson/Balaban semantics attached to the constructed fixed point.
------------------------------------------------------------------------

record PicardBackgroundData
    (Coarse State Tangent Bound : Set) : Set₁ where
  field
    core : PicardCoreData Coarse State Bound

    blockMap : State → Coarse
    reconstructFine : State → Tangent
    zeroBound : Bound
    actionFirstVariation : State → Tangent → Bound
    ConstraintTangent : State → Tangent → Set
    GaugeFixedBackground CandidateStationary : State → Set

    fixedImpliesConstraint : ∀ coarse state →
      criticalMap core coarse state ≡ state → blockMap state ≡ coarse
    fixedImpliesGaugeFixed : ∀ coarse state →
      criticalMap core coarse state ≡ state → GaugeFixedBackground state
    fixedImpliesStationary : ∀ coarse state →
      criticalMap core coarse state ≡ state →
      ∀ tangent → ConstraintTangent state tangent →
      actionFirstVariation state tangent ≡ zeroBound
    fixedImpliesCandidateStationary : ∀ coarse state →
      criticalMap core coarse state ≡ state → CandidateStationary state

    candidateStationaryImpliesFixed : ∀ coarse state →
      blockMap state ≡ coarse →
      GaugeFixedBackground state →
      CandidateStationary state →
      criticalMap core coarse state ≡ state

    BackgroundEquivalent : State → State → Set
    equivalentFromEquality : ∀ {left right} →
      left ≡ right → BackgroundEquivalent left right

    regularitySize : State → Bound
    coarseSmallness : Coarse → Bound
    regularityConstant : Bound
    picardLimitRegularity : ∀ coarse →
      LessEqual core
        (regularitySize (picardBackgroundCore core coarse))
        (scale core regularityConstant (coarseSmallness coarse))

open PicardBackgroundData public

picardBackground :
  ∀ {Coarse State Tangent Bound} →
  PicardBackgroundData Coarse State Tangent Bound → Coarse → State
picardBackground dataSet = picardBackgroundCore (core dataSet)

picardBackgroundFixed :
  ∀ {Coarse State Tangent Bound}
    (dataSet : PicardBackgroundData Coarse State Tangent Bound)
    coarse →
  criticalMap (core dataSet) coarse (picardBackground dataSet coarse)
  ≡ picardBackground dataSet coarse
picardBackgroundFixed dataSet = picardBackgroundCoreFixed (core dataSet)

backgroundSatisfiesConstraint :
  ∀ {Coarse State Tangent Bound}
    (dataSet : PicardBackgroundData Coarse State Tangent Bound)
    coarse →
  blockMap dataSet (picardBackground dataSet coarse) ≡ coarse
backgroundSatisfiesConstraint dataSet coarse =
  fixedImpliesConstraint dataSet coarse (picardBackground dataSet coarse)
    (picardBackgroundFixed dataSet coarse)

backgroundGaugeFixed :
  ∀ {Coarse State Tangent Bound}
    (dataSet : PicardBackgroundData Coarse State Tangent Bound)
    coarse →
  GaugeFixedBackground dataSet (picardBackground dataSet coarse)
backgroundGaugeFixed dataSet coarse =
  fixedImpliesGaugeFixed dataSet coarse (picardBackground dataSet coarse)
    (picardBackgroundFixed dataSet coarse)

backgroundStationary :
  ∀ {Coarse State Tangent Bound}
    (dataSet : PicardBackgroundData Coarse State Tangent Bound)
    coarse tangent →
  ConstraintTangent dataSet (picardBackground dataSet coarse) tangent →
  actionFirstVariation dataSet (picardBackground dataSet coarse) tangent
  ≡ zeroBound dataSet
backgroundStationary dataSet coarse tangent tangentConstraint =
  fixedImpliesStationary dataSet coarse (picardBackground dataSet coarse)
    (picardBackgroundFixed dataSet coarse) tangent tangentConstraint

backgroundCandidateStationary :
  ∀ {Coarse State Tangent Bound}
    (dataSet : PicardBackgroundData Coarse State Tangent Bound)
    coarse →
  CandidateStationary dataSet (picardBackground dataSet coarse)
backgroundCandidateStationary dataSet coarse =
  fixedImpliesCandidateStationary dataSet coarse
    (picardBackground dataSet coarse)
    (picardBackgroundFixed dataSet coarse)

minimizerUniqueModuloGauge :
  ∀ {Coarse State Tangent Bound}
    (dataSet : PicardBackgroundData Coarse State Tangent Bound)
    coarse candidate →
  blockMap dataSet candidate ≡ coarse →
  GaugeFixedBackground dataSet candidate →
  CandidateStationary dataSet candidate →
  BackgroundEquivalent dataSet candidate (picardBackground dataSet coarse)
minimizerUniqueModuloGauge dataSet coarse candidate constraint gauge stationary =
  equivalentFromEquality dataSet
    (fixedPointUniqueCore (core dataSet) coarse candidate
      (picardBackground dataSet coarse)
      (candidateStationaryImpliesFixed dataSet coarse candidate
        constraint gauge stationary)
      (picardBackgroundFixed dataSet coarse))

backgroundRegularity :
  ∀ {Coarse State Tangent Bound}
    (dataSet : PicardBackgroundData Coarse State Tangent Bound)
    coarse →
  LessEqual (core dataSet)
    (regularitySize dataSet (picardBackground dataSet coarse))
    (scale (core dataSet) (regularityConstant dataSet)
      (coarseSmallness dataSet coarse))
backgroundRegularity dataSet = picardLimitRegularity dataSet

picardRegularBackgroundConstruction :
  ∀ {Coarse State Tangent Bound} →
  PicardBackgroundData Coarse State Tangent Bound →
  P1.RegularBackgroundConstruction Coarse Tangent State Bound
picardRegularBackgroundConstruction dataSet = record
  { blockMap = blockMap dataSet
  ; backgroundOf = picardBackground dataSet
  ; reconstructFine = reconstructFine dataSet
  ; zeroBound = zeroBound dataSet
  ; actionFirstVariation =
      actionFirstVariation dataSet
  ; ConstraintTangent =
      ConstraintTangent dataSet
  ; GaugeFixedBackground =
      GaugeFixedBackground dataSet
  ; CandidateStationary =
      CandidateStationary dataSet
  ; backgroundSatisfiesConstraint =
      backgroundSatisfiesConstraint dataSet
  ; backgroundGaugeFixed =
      backgroundGaugeFixed dataSet
  ; backgroundStationary =
      backgroundStationary dataSet
  ; backgroundCandidateStationary =
      backgroundCandidateStationary dataSet
  ; BackgroundEquivalent =
      BackgroundEquivalent dataSet
  ; minimizerUniqueModuloGauge =
      minimizerUniqueModuloGauge dataSet
  ; regularitySize = regularitySize dataSet
  ; coarseSmallness = coarseSmallness dataSet
  ; regularityConstant =
      regularityConstant dataSet
  ; scale = scale (core dataSet)
  ; LessEqual = LessEqual (core dataSet)
  ; backgroundRegularity =
      backgroundRegularity dataSet
  }

p1PicardIterateConstructionLevel : ProofLevel
p1PicardIterateConstructionLevel = machineChecked

p1PicardFixedPointAndUniquenessLevel : ProofLevel
p1PicardFixedPointAndUniquenessLevel = machineChecked

p1PicardRegularBackgroundAdapterLevel : ProofLevel
p1PicardRegularBackgroundAdapterLevel = machineChecked

-- The literal Wilson critical-map contraction, completeness/locality laws and
-- fixed-point semantics remain the model-specific analytic inputs.
p1LiteralWilsonPicardInputsLevel : ProofLevel
p1LiteralWilsonPicardInputsLevel = conditional
