module DASHI.Physics.YangMills.BalabanClayP1PicardBackgroundConstructionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong₂; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP1BackgroundStabilityExact as P1

------------------------------------------------------------------------
-- Constructive Picard production of the nonlinear background.
--
-- The background is not a field of this record.  It is definitionally the limit
-- of the iterated critical map.  Completeness enters only through `limit` and
-- its two standard laws; the fixed-point, constraint, stationarity, uniqueness
-- and P1 adapter are then proved below.
------------------------------------------------------------------------

record PicardBackgroundData
    (Coarse State Tangent Bound : Set) : Set₁ where
  field
    criticalMap : Coarse → State → State
    seed : Coarse → State

    limit : (Nat → State) → State
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

    blockMap : State → Coarse
    reconstructFine : State → Tangent
    zeroBound : Bound
    actionFirstVariation : State → Tangent → Bound
    ConstraintTangent : State → Tangent → Set
    GaugeFixedBackground CandidateStationary : State → Set

    fixedImpliesConstraint : ∀ coarse state →
      criticalMap coarse state ≡ state → blockMap state ≡ coarse
    fixedImpliesGaugeFixed : ∀ coarse state →
      criticalMap coarse state ≡ state → GaugeFixedBackground state
    fixedImpliesStationary : ∀ coarse state →
      criticalMap coarse state ≡ state →
      ∀ tangent → ConstraintTangent state tangent →
      actionFirstVariation state tangent ≡ zeroBound
    fixedImpliesCandidateStationary : ∀ coarse state →
      criticalMap coarse state ≡ state → CandidateStationary state

    candidateStationaryImpliesFixed : ∀ coarse state →
      blockMap state ≡ coarse →
      GaugeFixedBackground state →
      CandidateStationary state →
      criticalMap coarse state ≡ state

    BackgroundEquivalent : State → State → Set
    equivalentFromEquality : ∀ {left right} →
      left ≡ right → BackgroundEquivalent left right

    regularitySize : State → Bound
    coarseSmallness : Coarse → Bound
    regularityConstant : Bound
    picardLimitRegularity : ∀ coarse →
      LessEqual
        (regularitySize (limit (λ depth →
          let
            iterate : Nat → State
            iterate zero = seed coarse
            iterate (suc n) = criticalMap coarse (iterate n)
          in iterate depth)))
        (scale regularityConstant (coarseSmallness coarse))

open PicardBackgroundData public

picard :
  ∀ {Coarse State Tangent Bound} →
  PicardBackgroundData Coarse State Tangent Bound →
  Coarse → Nat → State
picard dataSet coarse zero = seed dataSet coarse
picard dataSet coarse (suc depth) =
  criticalMap dataSet coarse (picard dataSet coarse depth)

picardStep :
  ∀ {Coarse State Tangent Bound}
    (dataSet : PicardBackgroundData Coarse State Tangent Bound)
    coarse depth →
  criticalMap dataSet coarse (picard dataSet coarse depth)
  ≡ picard dataSet coarse (suc depth)
picardStep dataSet coarse depth = Agda.Builtin.Equality.refl

picardBackground :
  ∀ {Coarse State Tangent Bound} →
  PicardBackgroundData Coarse State Tangent Bound →
  Coarse → State
picardBackground dataSet coarse =
  limit dataSet (picard dataSet coarse)

picardBackgroundFixed :
  ∀ {Coarse State Tangent Bound}
    (dataSet : PicardBackgroundData Coarse State Tangent Bound)
    coarse →
  criticalMap dataSet coarse (picardBackground dataSet coarse)
  ≡ picardBackground dataSet coarse
picardBackgroundFixed dataSet coarse =
  trans
    (mapCommutesWithLimit dataSet coarse (picard dataSet coarse))
    (tailShiftPreservesLimit dataSet (picard dataSet coarse))

fixedPointUnique :
  ∀ {Coarse State Tangent Bound}
    (dataSet : PicardBackgroundData Coarse State Tangent Bound)
    coarse left right →
  criticalMap dataSet coarse left ≡ left →
  criticalMap dataSet coarse right ≡ right →
  left ≡ right
fixedPointUnique dataSet coarse left right leftFixed rightFixed =
  strictShrinkForcesEquality dataSet left right
    (subst
      (λ value → LessEqual dataSet value
        (scale dataSet (rho dataSet) (distance dataSet left right)))
      (cong₂ (distance dataSet) leftFixed rightFixed)
      (contractive dataSet coarse left right))

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
    (fixedPointUnique dataSet coarse candidate
      (picardBackground dataSet coarse)
      (candidateStationaryImpliesFixed dataSet coarse candidate
        constraint gauge stationary)
      (picardBackgroundFixed dataSet coarse))

backgroundRegularity :
  ∀ {Coarse State Tangent Bound}
    (dataSet : PicardBackgroundData Coarse State Tangent Bound)
    coarse →
  LessEqual dataSet
    (regularitySize dataSet (picardBackground dataSet coarse))
    (scale dataSet (regularityConstant dataSet)
      (coarseSmallness dataSet coarse))
backgroundRegularity dataSet coarse = picardLimitRegularity dataSet coarse

picardRegularBackgroundConstruction :
  ∀ {Coarse State Tangent Bound} →
  PicardBackgroundData Coarse State Tangent Bound →
  P1.RegularBackgroundConstruction Coarse Tangent State Bound
picardRegularBackgroundConstruction dataSet = record
  { P1.RegularBackgroundConstruction.blockMap = blockMap dataSet
  ; P1.RegularBackgroundConstruction.backgroundOf = picardBackground dataSet
  ; P1.RegularBackgroundConstruction.reconstructFine = reconstructFine dataSet
  ; P1.RegularBackgroundConstruction.zeroBound = zeroBound dataSet
  ; P1.RegularBackgroundConstruction.actionFirstVariation =
      actionFirstVariation dataSet
  ; P1.RegularBackgroundConstruction.ConstraintTangent =
      ConstraintTangent dataSet
  ; P1.RegularBackgroundConstruction.GaugeFixedBackground =
      GaugeFixedBackground dataSet
  ; P1.RegularBackgroundConstruction.CandidateStationary =
      CandidateStationary dataSet
  ; P1.RegularBackgroundConstruction.backgroundSatisfiesConstraint =
      backgroundSatisfiesConstraint dataSet
  ; P1.RegularBackgroundConstruction.backgroundGaugeFixed =
      backgroundGaugeFixed dataSet
  ; P1.RegularBackgroundConstruction.backgroundStationary =
      backgroundStationary dataSet
  ; P1.RegularBackgroundConstruction.backgroundCandidateStationary =
      backgroundCandidateStationary dataSet
  ; P1.RegularBackgroundConstruction.BackgroundEquivalent =
      BackgroundEquivalent dataSet
  ; P1.RegularBackgroundConstruction.minimizerUniqueModuloGauge =
      minimizerUniqueModuloGauge dataSet
  ; P1.RegularBackgroundConstruction.regularitySize = regularitySize dataSet
  ; P1.RegularBackgroundConstruction.coarseSmallness = coarseSmallness dataSet
  ; P1.RegularBackgroundConstruction.regularityConstant =
      regularityConstant dataSet
  ; P1.RegularBackgroundConstruction.scale = scale dataSet
  ; P1.RegularBackgroundConstruction.LessEqual = LessEqual dataSet
  ; P1.RegularBackgroundConstruction.backgroundRegularity =
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
