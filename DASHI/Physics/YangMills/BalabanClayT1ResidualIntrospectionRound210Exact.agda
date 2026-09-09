{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT1ResidualIntrospectionRound210Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound207Exact as R207
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound209Exact as R209

data T1Residual210 : Set where
  globalMomentToEscapeControl : T1Residual210
  t1Closed : T1Residual210

data MissingCoordinate210 : Set where
  selectedGlobalSublevelContainmentSemantics : MissingCoordinate210
  noMissingCoordinate : MissingCoordinate210

data ProducerFamily210 : Set where
  globalSelectedMeasureMarkovContainment : ProducerFamily210
  selectedMeasureSupportGlobalization : ProducerFamily210
  directCompactContainmentTheorem : ProducerFamily210
  compileExistingUniformTightness : ProducerFamily210

record T1IntrospectiveState210 : Set where
  constructor t1-introspective-state-210
  field
    residual : T1Residual210
    missingCoordinate : MissingCoordinate210
    candidateProducer : ProducerFamily210
    producerPaysResidual : Bool

open T1IntrospectiveState210 public

currentT1IntrospectiveState210 : T1IntrospectiveState210
currentT1IntrospectiveState210 =
  t1-introspective-state-210
    globalMomentToEscapeControl
    selectedGlobalSublevelContainmentSemantics
    directCompactContainmentTheorem
    false

markovContainmentCandidate210 : T1IntrospectiveState210
markovContainmentCandidate210 =
  t1-introspective-state-210
    globalMomentToEscapeControl
    selectedGlobalSublevelContainmentSemantics
    globalSelectedMeasureMarkovContainment
    false

globalizationCandidate210 : T1IntrospectiveState210
globalizationCandidate210 =
  t1-introspective-state-210
    globalMomentToEscapeControl
    selectedGlobalSublevelContainmentSemantics
    selectedMeasureSupportGlobalization
    false

round207T1WallIsGlobalContainment :
  R207.preferredCurrentT1Status207 ≡ R207.missingGlobalMomentCompactContainment
round207T1WallIsGlobalContainment = refl

round209T1WallStillGlobalContainment :
  R209.preferredCurrentT1Status209 ≡ R209.missingGlobalMomentCompactContainment
round209T1WallStillGlobalContainment = refl

data LocalPath4CoercivityPaysGlobalT1Permission : Set where
data FiniteMomentAloneImpliesCompactContainmentPermission : Set where
data VisualizationPaysT1Permission : Set where
data CandidateProducerPaysT1Permission : Set where

localPath4CoercivityDoesNotPayGlobalT1 :
  LocalPath4CoercivityPaysGlobalT1Permission → ⊥
localPath4CoercivityDoesNotPayGlobalT1 ()

finiteMomentAloneDoesNotCreateCompactContainment :
  FiniteMomentAloneImpliesCompactContainmentPermission → ⊥
finiteMomentAloneDoesNotCreateCompactContainment ()

visualizationDoesNotPayT1 : VisualizationPaysT1Permission → ⊥
visualizationDoesNotPayT1 ()

candidateProducerDoesNotPayT1 : CandidateProducerPaysT1Permission → ⊥
candidateProducerDoesNotPayT1 ()

round210T234SearchSpaceAlreadyCompressedByR209 : Bool
round210T234SearchSpaceAlreadyCompressedByR209 = true

round210T1SearchSpaceReducedToGlobalContainmentSemantics : Bool
round210T1SearchSpaceReducedToGlobalContainmentSemantics = true

round210GlobalContainmentPaid : Bool
round210GlobalContainmentPaid = false

round210ClayPromotion : Bool
round210ClayPromotion = false

round210T1SearchSpaceReducedToGlobalContainmentSemanticsIsTrue :
  round210T1SearchSpaceReducedToGlobalContainmentSemantics ≡ true
round210T1SearchSpaceReducedToGlobalContainmentSemanticsIsTrue = refl

round210GlobalContainmentPaidIsFalse :
  round210GlobalContainmentPaid ≡ false
round210GlobalContainmentPaidIsFalse = refl

round210ClayPromotionIsFalse : round210ClayPromotion ≡ false
round210ClayPromotionIsFalse = refl
