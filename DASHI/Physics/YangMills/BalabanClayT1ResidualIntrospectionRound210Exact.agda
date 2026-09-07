{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT1ResidualIntrospectionRound210Exact where

------------------------------------------------------------------------
-- ROUND210: INTROSPECTIVE T1 SEARCH ON THE CURRENT T5 FRONTIER
--
-- R207 identified the genuine first global wall: the selected-measure moment
-- theorem must control escape from an admissible compact witness. R208/R209 then
-- compress T2/T3/T4 into weak-expectation/test-class semantics; they do not alter
-- T1. This owner makes the T1 search question explicit without identifying the
-- old local Path4 carrier with the selected global measure.
--
-- Physical intuition:
--   finite moment control says configurations cannot be too large too often;
--   compact containment additionally needs a *global observable/sublevel set*
--   whose outside region is exactly controlled by that moment on the selected
--   measure sequence. A local small-field coordinate theorem is insufficient
--   unless a separate support/globalization theorem connects the carriers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

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

-- Preferred first search: prove the needed global containment theorem directly
-- on the selected T5 measure carrier. Candidate selection is not payment.
currentT1IntrospectiveState210 : T1IntrospectiveState210
currentT1IntrospectiveState210 =
  t1-introspective-state-210
    globalMomentToEscapeControl
    selectedGlobalSublevelContainmentSemantics
    directCompactContainmentTheorem
    false

-- Two conditional alternatives remain legitimate search families but are not
-- silently promoted: a Markov/sublevel route needs global pointwise semantics;
-- a local coercivity route additionally needs selected-measure globalization.
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

------------------------------------------------------------------------
-- Cross-check the live frontier: R209 still has the exact same first T1 wall.
------------------------------------------------------------------------

round207T1WallIsGlobalContainment :
  R207.preferredCurrentT1Status207 ≡ R207.missingGlobalMomentCompactContainment
round207T1WallIsGlobalContainment = refl

round209T1WallStillGlobalContainment :
  R209.preferredCurrentT1Status209 ≡ R209.missingGlobalMomentCompactContainment
round209T1WallStillGlobalContainment = refl

------------------------------------------------------------------------
-- Firewalls revealed by the introspective comparison.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Progress accounting.
------------------------------------------------------------------------

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
