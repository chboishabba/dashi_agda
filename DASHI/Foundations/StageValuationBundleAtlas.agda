module DASHI.Foundations.StageValuationBundleAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import Base369 as Base
import DASHI.Core.DashiMarkov as Markov
open Markov.JoinedState
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas

------------------------------------------------------------------------
-- The local 0..11 atlas is a guarded transition chart, not a mandatory ladder.
------------------------------------------------------------------------

data StageRole : Set where
  rootCarrierRole : StageRole
  localUnitRole : StageRole
  relationOpenedRole : StageRole
  localClosureBarrierRole : StageRole
  tetralemmaInterpolationRole : StageRole
  decisionGateRole : StageRole
  reflexiveClosureBarrierRole : StageRole
  orbitProliferationRole : StageRole
  gluingResidualRole : StageRole
  systemicClosureBarrierRole : StageRole
  scalePromotedBundleRole : StageRole
  crossScaleFreshUnitRole : StageRole

stageRole : Atlas.StageAtlasZeroToEleven → StageRole
stageRole Atlas.atlas-0 = rootCarrierRole
stageRole Atlas.atlas-1 = localUnitRole
stageRole Atlas.atlas-2 = relationOpenedRole
stageRole Atlas.atlas-3 = localClosureBarrierRole
stageRole Atlas.atlas-4 = tetralemmaInterpolationRole
stageRole Atlas.atlas-5 = decisionGateRole
stageRole Atlas.atlas-6 = reflexiveClosureBarrierRole
stageRole Atlas.atlas-7 = orbitProliferationRole
stageRole Atlas.atlas-8 = gluingResidualRole
stageRole Atlas.atlas-9 = systemicClosureBarrierRole
stageRole Atlas.atlas-10 = scalePromotedBundleRole
stageRole Atlas.atlas-11 = crossScaleFreshUnitRole

data ClosureBand : Set where
  beforeFirstClosure : ClosureBand
  lowClosure3 : ClosureBand
  betweenLowAndMiddle : ClosureBand
  middleClosure6 : ClosureBand
  betweenMiddleAndHigh : ClosureBand
  highClosure9 : ClosureBand
  postClosureCarry : ClosureBand

closureBand : Atlas.StageAtlasZeroToEleven → ClosureBand
closureBand Atlas.atlas-0 = beforeFirstClosure
closureBand Atlas.atlas-1 = beforeFirstClosure
closureBand Atlas.atlas-2 = beforeFirstClosure
closureBand Atlas.atlas-3 = lowClosure3
closureBand Atlas.atlas-4 = betweenLowAndMiddle
closureBand Atlas.atlas-5 = betweenLowAndMiddle
closureBand Atlas.atlas-6 = middleClosure6
closureBand Atlas.atlas-7 = betweenMiddleAndHigh
closureBand Atlas.atlas-8 = betweenMiddleAndHigh
closureBand Atlas.atlas-9 = highClosure9
closureBand Atlas.atlas-10 = postClosureCarry
closureBand Atlas.atlas-11 = postClosureCarry

closureBandTone : ClosureBand → Base.TriTruth
closureBandTone lowClosure3 = Base.tri-low
closureBandTone middleClosure6 = Base.tri-mid
closureBandTone highClosure9 = Base.tri-high
closureBandTone beforeFirstClosure = Base.tri-low
closureBandTone betweenLowAndMiddle = Base.tri-mid
closureBandTone betweenMiddleAndHigh = Base.tri-high
closureBandTone postClosureCarry = Base.tri-low

stage3IsLowClosure :
  closureBand Atlas.atlas-3 ≡ lowClosure3
stage3IsLowClosure = refl

stage6IsMiddleClosure :
  closureBand Atlas.atlas-6 ≡ middleClosure6
stage6IsMiddleClosure = refl

stage9IsHighClosure :
  closureBand Atlas.atlas-9 ≡ highClosure9
stage9IsHighClosure = refl

------------------------------------------------------------------------
-- Memory, learning and unresolved residuals are coordinates of transition.
------------------------------------------------------------------------

record TransitionContext : Set where
  field
    currentStage : Atlas.StageAtlasZeroToEleven
    valuationDepth : Nat
    memoryDepth : Nat
    learningDepth : Nat
    activeFrame : String
    unresolvedResidualCount : Nat
    orientation : Base.TriTruth

StageJoinedState : Set
StageJoinedState =
  Markov.JoinedState
    Atlas.StageAtlasZeroToEleven
    Nat
    Nat
    Bool
    Bool

canonicalStageJoinedState : StageJoinedState
canonicalStageJoinedState = record
  { carrier = Atlas.atlas-3
  ; residual = 0
  ; obligations = 1
  ; authorities = false
  ; boundary = true
  }

data GuardedStageEdge :
  Atlas.StageAtlasZeroToEleven →
  Atlas.StageAtlasZeroToEleven →
  Set where
  instantiate : GuardedStageEdge Atlas.atlas-0 Atlas.atlas-1
  openRelation : GuardedStageEdge Atlas.atlas-1 Atlas.atlas-2
  articulateLocal : GuardedStageEdge Atlas.atlas-2 Atlas.atlas-3
  exposeCounterframe : GuardedStageEdge Atlas.atlas-3 Atlas.atlas-4
  preserveTetralemma : GuardedStageEdge Atlas.atlas-4 Atlas.atlas-5
  arrestedTetralemma : GuardedStageEdge Atlas.atlas-4 Atlas.atlas-1
  branchAfterDecision : GuardedStageEdge Atlas.atlas-5 Atlas.atlas-6
  prematureLocalCollapse : GuardedStageEdge Atlas.atlas-5 Atlas.atlas-3
  abandonAtDecision : GuardedStageEdge Atlas.atlas-5 Atlas.atlas-0
  inspectSheetExchange : GuardedStageEdge Atlas.atlas-6 Atlas.atlas-7
  reflexiveOscillation : GuardedStageEdge Atlas.atlas-6 Atlas.atlas-6
  isolateResidual : GuardedStageEdge Atlas.atlas-7 Atlas.atlas-8
  retainResidualInSynthesis : GuardedStageEdge Atlas.atlas-8 Atlas.atlas-9
  systemicSelfLoop : GuardedStageEdge Atlas.atlas-9 Atlas.atlas-9
  admitExternalCoordinate : GuardedStageEdge Atlas.atlas-9 Atlas.atlas-10
  addFreshLocalUnit : GuardedStageEdge Atlas.atlas-10 Atlas.atlas-11
  falseOverflowRestart : GuardedStageEdge Atlas.atlas-10 Atlas.atlas-1

record ValuationGuardedTransition : Set₁ where
  field
    source : Atlas.StageAtlasZeroToEleven
    target : Atlas.StageAtlasZeroToEleven
    edge : GuardedStageEdge source target
    requiredValuationDepth : Nat
    availableValuationDepth : Nat
    depthAdmissible : Bool
    memoryState : StageJoinedState
    learnedTransportAvailable : Bool
    residualRetained : Bool
    authorityPromoted : Bool

canonicalArrestedTetralemma : ValuationGuardedTransition
canonicalArrestedTetralemma = record
  { source = Atlas.atlas-4
  ; target = Atlas.atlas-1
  ; edge = arrestedTetralemma
  ; requiredValuationDepth = 4
  ; availableValuationDepth = 2
  ; depthAdmissible = false
  ; memoryState = canonicalStageJoinedState
  ; learnedTransportAvailable = false
  ; residualRetained = true
  ; authorityPromoted = false
  }

canonicalReflexiveOscillation : ValuationGuardedTransition
canonicalReflexiveOscillation = record
  { source = Atlas.atlas-6
  ; target = Atlas.atlas-6
  ; edge = reflexiveOscillation
  ; requiredValuationDepth = 6
  ; availableValuationDepth = 6
  ; depthAdmissible = true
  ; memoryState = canonicalStageJoinedState
  ; learnedTransportAvailable = false
  ; residualRetained = true
  ; authorityPromoted = false
  }

------------------------------------------------------------------------
-- Stage 8 owns a gluing residual. Decimal omission and the -1/2 mirror are
-- admissible observations, not causes or definitional identities.
------------------------------------------------------------------------

infix 4 _==_

_==_ : Nat → Nat → Bool
zero == zero = true
zero == suc _ = false
suc _ == zero = false
suc left == suc right = left == right

containsNat : Nat → List Nat → Bool
containsNat target [] = false
containsNat target (x ∷ xs) with target == x
... | true = true
... | false = containsNat target xs

oneOver81RepeatingBlock : List Nat
oneOver81RepeatingBlock =
  0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 9 ∷ []

digit8AbsentFromOneOver81Block :
  containsNat 8 oneOver81RepeatingBlock ≡ false
digit8AbsentFromOneOver81Block = refl

oneOver81DecimalCycleCertificate :
  81 * 12345679 ≡ 999999999
oneOver81DecimalCycleCertificate = refl

record Stage8ObstructionObservation : Set₁ where
  field
    stage : Atlas.StageAtlasZeroToEleven
    stageIs8 : stage ≡ Atlas.atlas-8
    missingAxisCount : Nat
    requiredAdditionalDepth : Nat
    residualEmitted : Bool
    scopeExceededAvailable : Bool
    refinementRequested : Bool
    decimalCycleCertificate :
      81 * 12345679 ≡ 999999999
    decimalOmissionWitness :
      containsNat 8 oneOver81RepeatingBlock ≡ false
    omissionCausesObstructionClaimed : Bool
    negativeHalfIdentifiedWithStage8Claimed : Bool

canonicalStage8ObstructionObservation :
  Stage8ObstructionObservation
canonicalStage8ObstructionObservation = record
  { stage = Atlas.atlas-8
  ; stageIs8 = refl
  ; missingAxisCount = 1
  ; requiredAdditionalDepth = 1
  ; residualEmitted = true
  ; scopeExceededAvailable = true
  ; refinementRequested = true
  ; decimalCycleCertificate = oneOver81DecimalCycleCertificate
  ; decimalOmissionWitness = digit8AbsentFromOneOver81Block
  ; omissionCausesObstructionClaimed = false
  ; negativeHalfIdentifiedWithStage8Claimed = false
  }

------------------------------------------------------------------------
-- Place-value bundling and Stage 11 as a cross-scale overlap.
------------------------------------------------------------------------

placeBundleCount : Nat → Nat → Nat
placeBundleCount base depth = base ^ depth

record PlaceBundle : Set where
  field
    base : Nat
    depth : Nat
    fineUnitCount : Nat
    countExact :
      fineUnitCount ≡ placeBundleCount base depth
    lowerPlaceEmptyInCoarseLabel : Bool
    bundlePromotedToNextScale : Bool

decimalOneBundle : PlaceBundle
decimalOneBundle = record
  { base = 10
  ; depth = 0
  ; fineUnitCount = 1
  ; countExact = refl
  ; lowerPlaceEmptyInCoarseLabel = false
  ; bundlePromotedToNextScale = false
  }

decimalTenBundle : PlaceBundle
decimalTenBundle = record
  { base = 10
  ; depth = 1
  ; fineUnitCount = 10
  ; countExact = refl
  ; lowerPlaceEmptyInCoarseLabel = true
  ; bundlePromotedToNextScale = true
  }

decimalHundredBundle : PlaceBundle
decimalHundredBundle = record
  { base = 10
  ; depth = 2
  ; fineUnitCount = 100
  ; countExact = refl
  ; lowerPlaceEmptyInCoarseLabel = true
  ; bundlePromotedToNextScale = true
  }

hundredIsTenBundlesOfTen :
  100 ≡ 10 * 10
hundredIsTenBundlesOfTen = refl

record BundleSheaf
  (BasePoint LocalSection GlobalSection : Set) : Set₁ where
  field
    restrict : GlobalSection → BasePoint → LocalSection
    compatible : (BasePoint → LocalSection) → Set
    glue : (locals : BasePoint → LocalSection) →
      compatible locals →
      GlobalSection
    glueRestricts :
      ∀ locals witness point →
      restrict (glue locals witness) point ≡ locals point

record Stage11CrossScaleJoin : Set where
  field
    stage : Atlas.StageAtlasZeroToEleven
    stageIs11 : stage ≡ Atlas.atlas-11
    carriedBundleValue : Nat
    freshLocalValue : Nat
    joinedValue : Nat
    carriedIsTen : carriedBundleValue ≡ 10
    freshIsOne : freshLocalValue ≡ 1
    joinIsEleven :
      carriedBundleValue + freshLocalValue ≡ joinedValue
    coarseBundle : PlaceBundle
    coarseBundleMatchesCarriedValue :
      PlaceBundle.fineUnitCount coarseBundle ≡ carriedBundleValue
    manifoldRequiresGluingWitness : Bool
    manifoldFromNumeralAloneClaimed : Bool

canonicalStage11CrossScaleJoin : Stage11CrossScaleJoin
canonicalStage11CrossScaleJoin = record
  { stage = Atlas.atlas-11
  ; stageIs11 = refl
  ; carriedBundleValue = 10
  ; freshLocalValue = 1
  ; joinedValue = 11
  ; carriedIsTen = refl
  ; freshIsOne = refl
  ; joinIsEleven = refl
  ; coarseBundle = decimalTenBundle
  ; coarseBundleMatchesCarriedValue = refl
  ; manifoldRequiresGluingWitness = true
  ; manifoldFromNumeralAloneClaimed = false
  }

------------------------------------------------------------------------
-- The local atlas is unbounded by place-value recursion.
------------------------------------------------------------------------

record DecimalStageAddress : Set where
  field
    coarseBundles : Nat
    localOffset : Nat
    globalIndex : Nat
    decomposition :
      10 * coarseBundles + localOffset ≡ globalIndex

stage14Address : DecimalStageAddress
stage14Address = record
  { coarseBundles = 1
  ; localOffset = 4
  ; globalIndex = 14
  ; decomposition = refl
  }

stage17Address : DecimalStageAddress
stage17Address = record
  { coarseBundles = 1
  ; localOffset = 7
  ; globalIndex = 17
  ; decomposition = refl
  }

stage200Address : DecimalStageAddress
stage200Address = record
  { coarseBundles = 20
  ; localOffset = 0
  ; globalIndex = 200
  ; decomposition = refl
  }

record CompressedStageTransition : Set₁ where
  field
    source : DecimalStageAddress
    target : DecimalStageAddress
    hiddenLocalPath : List Atlas.StageAtlasZeroToEleven
    valuationDepth : Nat
    memoryReceipt : StageJoinedState
    learningAdapterAvailable : Bool
    priorDialecticsReused : Bool
    unresolvedResidualsRetained : Bool
    intermediateWorkAbsentClaimed : Bool
    semanticAuthorityPromoted : Bool

canonicalTransformativeJump3To14 :
  CompressedStageTransition
canonicalTransformativeJump3To14 = record
  { source = record
      { coarseBundles = 0
      ; localOffset = 3
      ; globalIndex = 3
      ; decomposition = refl
      }
  ; target = stage14Address
  ; hiddenLocalPath =
      Atlas.atlas-3
      ∷ Atlas.atlas-4
      ∷ Atlas.atlas-5
      ∷ Atlas.atlas-6
      ∷ Atlas.atlas-7
      ∷ Atlas.atlas-8
      ∷ Atlas.atlas-9
      ∷ Atlas.atlas-10
      ∷ Atlas.atlas-11
      ∷ []
  ; valuationDepth = 11
  ; memoryReceipt = canonicalStageJoinedState
  ; learningAdapterAvailable = true
  ; priorDialecticsReused = true
  ; unresolvedResidualsRetained = true
  ; intermediateWorkAbsentClaimed = false
  ; semanticAuthorityPromoted = false
  }

record StageValuationAuthorityBoundary : Set where
  field
    atlasIsMandatoryLinearLadder : Bool
    stageNumberAloneAuthorisesTransition : Bool
    memoryAndLearningCanCompressPath : Bool
    observedJumpMeansNoIntermediateWork : Bool
    stage11IsMaximum : Bool
    closure369BandsAreExplicit : Bool
    balancedTernaryOrientationIsSeparate : Bool

canonicalStageValuationAuthorityBoundary :
  StageValuationAuthorityBoundary
canonicalStageValuationAuthorityBoundary = record
  { atlasIsMandatoryLinearLadder = false
  ; stageNumberAloneAuthorisesTransition = false
  ; memoryAndLearningCanCompressPath = true
  ; observedJumpMeansNoIntermediateWork = false
  ; stage11IsMaximum = false
  ; closure369BandsAreExplicit = true
  ; balancedTernaryOrientationIsSeparate = true
  }
