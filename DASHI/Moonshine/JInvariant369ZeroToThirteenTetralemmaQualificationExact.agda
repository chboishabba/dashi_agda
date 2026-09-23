module DASHI.Moonshine.JInvariant369ZeroToThirteenTetralemmaQualificationExact where

------------------------------------------------------------------------
-- 0..13 / TETRALEMMA / SIXFOLD QUALIFICATION FOR THE CONSOLIDATED 369/J STATE
--
-- The repo contains several numerically adjacent but semantically distinct
-- structures:
--
--   * rank/index atlas 0..13, with exact ternary place values in 1,3,9;
--   * guarded stage atlas 0..12, with stage-specific transition roles;
--   * a ternary 27-cell synthesis carrier;
--   * a four-position tetralemma support square;
--   * a sixfold bounded meta-status carrier;
--   * the consolidated modular/J + Stage12/144 + signed-SSP state.
--
-- This module keeps all of those coordinates, and proves the available
-- crosswalks, without collapsing them by shared numbers.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Moonshine.JInvariant369ConsolidatedNextStageExact as Consolidated
import DASHI.Moonshine.JInvariantFormulaic369RendererExact as Render
import DASHI.Wikimedia.IbrahimEnZeroToThirteenNDimOEISHyperfabricSnowballExact as Rank
import DASHI.Wikimedia.IbrahimZeroToThirteenTernaryCarryNDimFibreSnowballExact as Carry
import DASHI.Foundations.StageAtlasZeroToTwelve as Stage
import DASHI.Foundations.StageValuationBundleAtlas as LegacyStage
import DASHI.Foundations.StageAtlasZeroToEleven as Atlas
import DASHI.Biology.RelationalAppraisalPointedPhaseExact as Rel
import DASHI.Foundations.StageTetralemmaArrestBridge as Arrest
import DASHI.Foundations.DialecticCubieTetralemmaExact as Tetra
import DASHI.Algebra.SixfoldLogic as Six
import DASHI.Reasoning.TernarySynthesisLogicQualificationExact as Qualification
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Synthesis
import DASHI.Foundations.StageTwelveGrothendieckRelationHyperformExact as Stage12

------------------------------------------------------------------------
-- 1. Exact 0..13 ternary address atlas.
------------------------------------------------------------------------

rank0Row  = Carry.r0
rank1Row  = Carry.r1
rank2Row  = Carry.r2
rank3Row  = Carry.r3
rank4Row  = Carry.r4
rank5Row  = Carry.r5
rank6Row  = Carry.r6
rank7Row  = Carry.r7
rank8Row  = Carry.r8
rank9Row  = Carry.r9
rank10Row = Carry.r10
rank11Row = Carry.r11
rank12Row = Carry.r12
rank13Row = Carry.r13

rank12Address110 :
  Carry.renderedBase3 rank12Row ≡ "110"
rank12Address110 = refl

rank13Address111 :
  Carry.renderedBase3 rank13Row ≡ "111"
rank13Address111 = refl

rank12IsThreePlusNine :
  12 ≡ 3 + 9
rank12IsThreePlusNine =
  Carry.twelveAsThreePlusNine

rank13IsOnePlusThreePlusNine :
  13 ≡ 1 + 3 + 9
rank13IsOnePlusThreePlusNine =
  Carry.thirteenAsOnePlusThreePlusNine

rank12ProfilesAre531441 :
  Rank.fixedTernaryProfileCount Rank.rank12 ≡ 531441
rank12ProfilesAre531441 =
  Rank.rank12Profiles

rank13ProfilesAre1594323 :
  Rank.fixedTernaryProfileCount Rank.rank13 ≡ 1594323
rank13ProfilesAre1594323 =
  Rank.rank13Profiles

------------------------------------------------------------------------
-- 2. Rank-12 / rank-13 count crosswalks already paid by the Stage12 owner.
------------------------------------------------------------------------

rank12MatchesCompleteRelationalCycleCount :
  Rank.fixedTernaryProfileCount Rank.rank12
  ≡
  Rel.completeCycleStateCount
rank12MatchesCompleteRelationalCycleCount =
  sym Stage12.completeCycleMatchesRank12ProfileCount

rank13MatchesCentralCompletionCount :
  Rank.fixedTernaryProfileCount Rank.rank13
  ≡
  Rel.centralCompletionGroupOrderPattern
rank13MatchesCentralCompletionCount =
  sym Stage12.centralCompletionMatchesRank13ProfileCount

------------------------------------------------------------------------
-- 3. Guarded stage semantics are separate from the rank/index atlas.
------------------------------------------------------------------------

stage4CarriesTetralemmaInterpolationRole :
  LegacyStage.stageRole Atlas.atlas-4
  ≡ LegacyStage.tetralemmaInterpolationRole
stage4CarriesTetralemmaInterpolationRole = refl

stage6CarriesReflexiveClosureRole :
  LegacyStage.stageRole Atlas.atlas-6
  ≡ LegacyStage.reflexiveClosureBarrierRole
stage6CarriesReflexiveClosureRole = refl

stage9CarriesSystemicClosureRole :
  LegacyStage.stageRole Atlas.atlas-9
  ≡ LegacyStage.systemicClosureBarrierRole
stage9CarriesSystemicClosureRole = refl

stage12OpensRelationAtScale :
  Stage.recursiveRole Stage.stage-12
  ≡ Stage.relationOpenedAtScale
stage12OpensRelationAtScale =
  Stage.stage12OpensRelationAtNewScale

stage4ArrestReceipt :
  Arrest.TetralemmaArrestReceipt
stage4ArrestReceipt =
  Arrest.canonicalTetralemmaArrestReceipt

------------------------------------------------------------------------
-- 4. Tetralemma is a retained qualification over a 27-cell synthesis carrier.
------------------------------------------------------------------------

TetralemmaQualified27 : Set
TetralemmaQualified27 =
  Qualification.TetralemmaQualifiedSynthesis

SixfoldQualified27 : Set
SixfoldQualified27 =
  Qualification.SixfoldQualifiedSynthesis

qualifyPositionOnly :
  Synthesis.SynthesisChoice27 →
  TetralemmaQualified27
qualifyPositionOnly =
  Qualification.positionOnlyQualification

qualifyCounterpositionOnly :
  Synthesis.SynthesisChoice27 →
  TetralemmaQualified27
qualifyCounterpositionOnly =
  Qualification.counterpositionOnlyQualification

qualifyBoth :
  Synthesis.SynthesisChoice27 →
  TetralemmaQualified27
qualifyBoth =
  Qualification.bothSupportedQualification

qualifyNeither :
  Synthesis.SynthesisChoice27 →
  TetralemmaQualified27
qualifyNeither =
  Qualification.neitherEstablishedQualification

tetralemmaPreservesUnderlying27Carrier :
  (synthesis : Synthesis.SynthesisChoice27) →
  (square : Tetra.SupportCounterSquare) →
  Qualification.synthesisCarrier
    (Qualification.qualifyTetralemma synthesis square)
  ≡ synthesis
tetralemmaPreservesUnderlying27Carrier =
  Qualification.qualificationPreservesSynthesis

bothAndNeitherRemainDistinctQualifications :
  (synthesis : Synthesis.SynthesisChoice27) →
  Qualification.tetralemmaPosition (qualifyBoth synthesis)
  ≡ Tetra.bothSupported
  ×
  Qualification.tetralemmaPosition (qualifyNeither synthesis)
  ≡ Tetra.neitherEstablished
bothAndNeitherRemainDistinctQualifications synthesis =
  Qualification.bothPositionIsBothSupported synthesis
  ,
  Qualification.neitherPositionIsNeitherEstablished synthesis

sixfoldRetainsTetralemmaQualifiedCarrier :
  (qualified : TetralemmaQualified27) →
  (status : Six.Stage6) →
  Qualification.tetralemmaQualified
    (Qualification.qualifySixfold qualified status)
  ≡ qualified
sixfoldRetainsTetralemmaQualifiedCarrier =
  Qualification.sixfoldQualificationPreservesTetralemmaCarrier

------------------------------------------------------------------------
-- 5. The consolidated J/SSP state can be qualified without rewriting it.
------------------------------------------------------------------------

record QualifiedConsolidated369State
    (R : Render.JPhaseRenderingAlgebra) : Set where
  constructor qualified-consolidated369-state
  field
    consolidatedState :
      Consolidated.Consolidated369State R

    rankCoordinate :
      Rank.RankZeroToThirteen

    stageCoordinate :
      Stage.StageAtlasZeroToTwelve

    logicalQualification :
      SixfoldQualified27

open QualifiedConsolidated369State public

forgetQualification :
  ∀ {R} →
  QualifiedConsolidated369State R →
  Consolidated.Consolidated369State R
forgetQualification =
  consolidatedState

qualificationDoesNotRewriteConsolidatedState :
  ∀ {R}
    (state : Consolidated.Consolidated369State R)
    (rank : Rank.RankZeroToThirteen)
    (stage : Stage.StageAtlasZeroToTwelve)
    (logic : SixfoldQualified27) →
  forgetQualification
    (qualified-consolidated369-state state rank stage logic)
  ≡ state
qualificationDoesNotRewriteConsolidatedState state rank stage logic = refl

------------------------------------------------------------------------
-- 6. A canonical relation-opening annotation uses rank 12 / stage 12,
--    but this is a typed pairing, not a proof that rank and stage are identical
--    semantic objects.
------------------------------------------------------------------------

relationOpeningQualification :
  ∀ {R} →
  Consolidated.Consolidated369State R →
  SixfoldQualified27 →
  QualifiedConsolidated369State R
relationOpeningQualification state logic =
  qualified-consolidated369-state
    state
    Rank.rank12
    Stage.stage-12
    logic

relationOpeningHasRank12 :
  ∀ {R}
    (state : Consolidated.Consolidated369State R)
    (logic : SixfoldQualified27) →
  rankCoordinate (relationOpeningQualification state logic)
  ≡ Rank.rank12
relationOpeningHasRank12 state logic = refl

relationOpeningHasStage12 :
  ∀ {R}
    (state : Consolidated.Consolidated369State R)
    (logic : SixfoldQualified27) →
  stageCoordinate (relationOpeningQualification state logic)
  ≡ Stage.stage-12
relationOpeningHasStage12 state logic = refl

------------------------------------------------------------------------
-- 7. WrongType firewalls: equal numbers / equal cardinalities do not collapse
--    these carriers.
------------------------------------------------------------------------

data Rank12EqualsStage12SemanticIdentity : Set where
data TetralemmaEqualsTernary27Carrier : Set where
data SixfoldEqualsPhase6Carrier : Set where
data JLocal27EqualsSynthesisChoice27 : Set where
data Rank13CreatesStage13SemanticRole : Set where

rank12DoesNotCreateStage12SemanticIdentity :
  Rank12EqualsStage12SemanticIdentity → ⊥
rank12DoesNotCreateStage12SemanticIdentity ()

tetralemmaDoesNotReplaceTernary27 :
  TetralemmaEqualsTernary27Carrier → ⊥
tetralemmaDoesNotReplaceTernary27 ()

sixfoldDoesNotCreatePhase6Identity :
  SixfoldEqualsPhase6Carrier → ⊥
sixfoldDoesNotCreatePhase6Identity ()

local27DoesNotCreateSynthesis27Identity :
  JLocal27EqualsSynthesisChoice27 → ⊥
local27DoesNotCreateSynthesis27Identity ()

rank13DoesNotInventStage13Semantics :
  Rank13CreatesStage13SemanticRole → ⊥
rank13DoesNotInventStage13Semantics ()

------------------------------------------------------------------------
-- 8. Exact boundary receipt.
------------------------------------------------------------------------

record ZeroToThirteenTetralemma369Boundary : Set where
  constructor zero-to-thirteen-tetralemma-369-boundary
  field
    exactTernaryRows0to13Reused : Bool
    rank12Address110Paid : Bool
    rank13Address111Paid : Bool
    rank12Profile531441Paid : Bool
    rank13Profile1594323Paid : Bool

    stage4TetralemmaRolePaid : Bool
    stage6ReflexiveClosureRolePaid : Bool
    stage9SystemicClosureRolePaid : Bool
    stage12RelationOpeningRolePaid : Bool
    arrestedTetralemmaReceiptReused : Bool

    tetralemmaRetains27Carrier : Bool
    bothAndNeitherRemainDistinct : Bool
    sixfoldRetainsTetralemmaCarrier : Bool
    qualificationRetainsConsolidatedState : Bool

    rank12EqualsStage12ByMeaning : Bool
    tetralemmaEqualsTernaryCarrier : Bool
    sixfoldEqualsModularPhase6 : Bool
    localJ27EqualsSynthesis27 : Bool
    rank13CreatesStage13Semantics : Bool

open ZeroToThirteenTetralemma369Boundary public

canonicalZeroToThirteenTetralemma369Boundary :
  ZeroToThirteenTetralemma369Boundary
canonicalZeroToThirteenTetralemma369Boundary =
  zero-to-thirteen-tetralemma-369-boundary
    true true true true true
    true true true true true
    true true true true
    false false false false false
