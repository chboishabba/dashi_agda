module DASHI.Interop.BodyKeepsScoreStageCarryBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Core.AuthorityNonPromotionCore as Authority
import DASHI.Interop.BodyKeepsScoreCandidateBoundary as BodyScore
import DASHI.Interop.BodyKeepsScoreResidualGeometry as Geometry

------------------------------------------------------------------------
-- Stage 0..11 and j+1 carry bridge for the body-score candidate lane.
--
-- Stage 8 is a failed gluing state, never a person classification.  Stage 9
-- is a local receipt, Stage 10 introduces a new safety convention, and Stage
-- 11 records the multi-chart gluing obligation.  j+1 is a candidate carry,
-- not treatment, cure, forced disclosure, or clinical promotion.


data BodyScoreCarryKind : Set where
  noCarry : BodyScoreCarryKind
  localReceiptCarry : BodyScoreCarryKind
  newChartCarry : BodyScoreCarryKind
  manifoldGluingCarry : BodyScoreCarryKind

record BodyScoreStageRow : Set where
  constructor mkBodyScoreStageRow
  field
    stageIndex : Nat
    stage : BodyScore.BodyScoreStage
    stageLabel : String
    carryKind : BodyScoreCarryKind
    personClassification : Bool
    personClassificationIsFalse : personClassification ≡ false
    clinicalInstruction : Bool
    clinicalInstructionIsFalse : clinicalInstruction ≡ false

open BodyScoreStageRow public

canonicalBodyScoreStageRows : List BodyScoreStageRow
canonicalBodyScoreStageRows =
  mkBodyScoreStageRow zero BodyScore.unmarkedBodyGroundStage
    "0: unmarked body ground" noCarry false refl false refl
  ∷ mkBodyScoreStageRow (suc zero) BodyScore.firstFeltMarkStage
    "1: first felt mark" noCarry false refl false refl
  ∷ mkBodyScoreStageRow (suc (suc zero)) BodyScore.selfWorldDyadStage
    "2: self/world dyad" noCarry false refl false refl
  ∷ mkBodyScoreStageRow (suc (suc (suc zero))) BodyScore.compiledInverseTriadStage
    "3: self/world/world^-1 compiled triad" noCarry false refl false refl
  ∷ mkBodyScoreStageRow 4 BodyScore.survivalCycleStage
    "4: survival response cycle" noCarry false refl false refl
  ∷ mkBodyScoreStageRow 5 BodyScore.decisionThresholdStage
    "5: pause/continue/orient/stop threshold" noCarry false refl false refl
  ∷ mkBodyScoreStageRow 6 BodyScore.oldInverseCurrentWorldTensionStage
    "6: old inverse/current world tension" noCarry false refl false refl
  ∷ mkBodyScoreStageRow 7 BodyScore.maximumBoundaryPressureStage
    "7: maximum unresolved boundary pressure" noCarry false refl false refl
  ∷ mkBodyScoreStageRow 8 BodyScore.failedGluingStage
    "8: failed gluing / no safe adapter" noCarry false refl false refl
  ∷ mkBodyScoreStageRow 9 BodyScore.localIntegrationReceiptStage
    "9: local integration receipt" localReceiptCarry false refl false refl
  ∷ mkBodyScoreStageRow 10 BodyScore.newSafetyConventionStage
    "10: j+1 new safety convention" newChartCarry false refl false refl
  ∷ mkBodyScoreStageRow 11 BodyScore.manifoldChartGluingStage
    "11: body/narrative/relational chart gluing" manifoldGluingCarry false refl false refl
  ∷ []

record BodyScoreStageCarryBridge : Set₁ where
  constructor mkBodyScoreStageCarryBridge
  field
    bodyScoreBoundary :
      BodyScore.BodyKeepsScoreCandidateBoundary

    residualGeometry :
      Geometry.BodyScoreResidualGeometry

    stageRows :
      List BodyScoreStageRow

    stageRowsAreCanonical :
      stageRows ≡ canonicalBodyScoreStageRows

    currentChartIndex :
      Nat

    nextChartIndex :
      Nat

    nextChartIsSuccessor :
      nextChartIndex ≡ suc currentChartIndex

    jPlusOneReading :
      String

    stageEightClassifiesPerson :
      Bool

    stageEightClassifiesPersonIsFalse :
      stageEightClassifiesPerson ≡ false

    jPlusOneIsTreatment :
      Bool

    jPlusOneIsTreatmentIsFalse :
      jPlusOneIsTreatment ≡ false

    jPlusOneIsCure :
      Bool

    jPlusOneIsCureIsFalse :
      jPlusOneIsCure ≡ false

    authorityBundle :
      Authority.AuthorityNonPromotionBundle

    clinicalAuthorityIsFalse :
      Authority.authorityFlag Authority.clinicalAuthority authorityBundle ≡ false

open BodyScoreStageCarryBridge public

bodyScoreStageCarryAuthority : Authority.AuthorityNonPromotionBundle
bodyScoreStageCarryAuthority =
  Authority.mkClosedAuthorityNonPromotionBundle
    "body-score stage/carry bridge: candidate-only"

canonicalBodyScoreStageCarryBridge : BodyScoreStageCarryBridge
canonicalBodyScoreStageCarryBridge =
  mkBodyScoreStageCarryBridge
    BodyScore.canonicalBodyKeepsScoreCandidateBoundary
    Geometry.canonicalBodyScoreResidualGeometry
    canonicalBodyScoreStageRows
    refl
    zero
    (suc zero)
    refl
    "j+1 is a candidate re-charting obligation when the old compiled inverse fails to glue to the current world"
    false
    refl
    false
    refl
    false
    refl
    bodyScoreStageCarryAuthority
    (Authority.authorityFlagIsFalse Authority.clinicalAuthority bodyScoreStageCarryAuthority)

canonicalStageEightIsNotPersonClassification :
  stageEightClassifiesPerson canonicalBodyScoreStageCarryBridge ≡ false
canonicalStageEightIsNotPersonClassification =
  stageEightClassifiesPersonIsFalse canonicalBodyScoreStageCarryBridge

canonicalJPlusOneIsNotTreatment :
  jPlusOneIsTreatment canonicalBodyScoreStageCarryBridge ≡ false
canonicalJPlusOneIsNotTreatment =
  jPlusOneIsTreatmentIsFalse canonicalBodyScoreStageCarryBridge
