module DASHI.Reasoning.KantLacanRegression where

open import DASHI.Core.Prelude

import Moonshine as Moon
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Foundations.JPlusOneScaleBridge as JPlus
import DASHI.Foundations.StageAtlasZeroToTwelve as Stage
import DASHI.Foundations.StageCantorScaleRecursion as StageCantor
import DASHI.Foundations.StageZeroToTwelveTransitionCore as Transition
import DASHI.Reasoning.KantCriticalCompiler as Kant
import DASHI.Reasoning.KantLacanSourceAtlas as Sources
import DASHI.Reasoning.KantLacanZizekRuntime as Runtime
import DASHI.Reasoning.LacanCapitalistDiscourseMutation as Capitalist
import DASHI.Reasoning.LacanDiscourseMatheme as Discourse
import DASHI.Reasoning.LacanRegisterSinthomeHyperfabric as RSI
import DASHI.Reasoning.LacanSignifierSubjectCore as Lacan
import DASHI.Reasoning.StageZeroToTwelveKantLacanZizekBridge as StageBridge

------------------------------------------------------------------------
-- Exact regression anchors.
------------------------------------------------------------------------

stage12IndexIsTwelve :
  Stage.toNat Stage.stage-12 ≡ 12
stage12IndexIsTwelve = refl

stage11IsJPlusOne :
  Stage.decimalCarryUnit + Stage.localJUnit ≡ Stage.toNat Stage.stage-11
stage11IsJPlusOne = Stage.stage11IsOneJPlusOne

stage12IsJPlusTwo :
  Stage.decimalCarryUnit + 2 * Stage.localJUnit ≡ Stage.toNat Stage.stage-12
stage12IsJPlusTwo = Stage.stage12IsOneJPlusTwo

stage11To12GuardedTarget :
  Transition.GuardedStage012Transition.target
    Transition.canonicalStage11To12Transition
  ≡ Stage.stage-12
stage11To12GuardedTarget = refl

mckayArithmeticStillExact :
  Moon.rep-dim + 1 ≡ Moon.j-coefficient
mckayArithmeticStillExact = Moon.mckay

standardDiscourseRotationHasOrderFour :
  ∀ discourse →
  Discourse.rotate
    (Discourse.rotate
      (Discourse.rotate
        (Discourse.rotate discourse)))
  ≡ discourse
standardDiscourseRotationHasOrderFour =
  Discourse.rotateFourTimesIsIdentity

masterAgentOrbitRegression :
  Discourse.orbitAt Discourse.agent Discourse.masterDiscourse
  ≡ Lacan.masterSignifier
  ∷ Lacan.barredSubjectTerm
  ∷ Lacan.objetATerm
  ∷ Lacan.knowledgeNetwork
  ∷ []
masterAgentOrbitRegression =
  Discourse.CompleteMasterOrbit.agentOrbit
    Discourse.canonicalCompleteMasterOrbit

reflectiveJudgmentDoesNotPromote :
  Kant.KantCriticalCompilerBoundary.reflectiveJudgmentDirectlyPromotes
    Kant.canonicalKantCriticalCompilerBoundary
  ≡ false
reflectiveJudgmentDoesNotPromote = refl

capitalistMutationNotStandardFourCycle :
  Capitalist.CapitalistMutationReceipt.standardFourCyclePreservedClaimed
    Capitalist.canonicalCapitalistMutationReceipt
  ≡ false
capitalistMutationNotStandardFourCycle = refl

borromeanTopologyRemainsOpen :
  RSI.RSIHyperlink.borromeanTopologicalLinkProved
    RSI.canonicalRSIHyperlink
  ≡ false
borromeanTopologyRemainsOpen = refl

runtimeDoesNotDiagnose :
  Runtime.KantLacanZizekAuthorityBoundary.runtimeDiagnosesSubject
    Runtime.canonicalKantLacanZizekAuthorityBoundary
  ≡ false
runtimeDoesNotDiagnose = refl

stage012CountIsThirteen :
  StageBridge.canonicalStage012RowCount ≡ 13
stage012CountIsThirteen = refl

sourceAtlasCountIsNine :
  Source.sourceCount Sources.kantLacanSources ≡ 9
sourceAtlasCountIsNine = refl

jScaleNotModularJ :
  JPlus.JPlusOneAuthorityBoundary.modularJEqualsLocalJUnitClaimed
    JPlus.canonicalJPlusOneAuthorityBoundary
  ≡ false
jScaleNotModularJ = refl

stageCantorDoesNotNameAlephOne :
  StageCantor.StageCantorScaleAuthorityBoundary.stageElevenEqualsAlephOne
    StageCantor.canonicalStageCantorScaleAuthorityBoundary
  ≡ false
stageCantorDoesNotNameAlephOne = refl
