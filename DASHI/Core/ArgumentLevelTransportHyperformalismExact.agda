module DASHI.Core.ArgumentLevelTransportHyperformalismExact where

------------------------------------------------------------------------
-- PROVENANCE-PRESERVING ARGUMENT LEVEL TRANSPORT
--
-- The repository already distinguishes:
--
--   * an argument from an obstruction to transporting that argument;
--   * NO_TYPED_MEET at the current inspection from eternal impossibility;
--   * same-fibre typed-meet failure from SCOPE_EXCEEDED;
--   * suppression/pruning from semantic refutation;
--   * residual as unexplained information from semantic erasure;
--   * j+1 as a typed successor/rechart from modular-j or representation labels.
--
-- This module welds those existing contracts into one small generic carrier:
-- an argument may move to another inspection/chart/role level while the whole
-- argument and its provenance are retained exactly.  Local evidence and local
-- applicability are stalk data; neither replaces the retained argument.
--
-- The 369, carry-memory, and Moonshine/J+1 modules are consumed below only as
-- exact carrier/extension examples.  No historical or semantic identification
-- between those lanes is asserted.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ArgumentObstructionCore as Argument
import DASHI.Core.RequiredAxisSupportSquareExact as Support
import DASHI.Interop.InspectionRelativeNoTypedMeet as Inspect
import DASHI.Interop.PNFVoidScopeBoundary as Scope
import DASHI.Cognition.PNF.ReopenableEvidenceFibre as Reopen
import DASHI.Foundations.JChartSuccessorBoundary as Chart
import DASHI.Dynamics.TriadicResidualRechartDynamics as Rechart
import DASHI.Reasoning.CarryMemorySubvoxelReceipt as Carry
import DASHI.Interop.PNFHyperfabric369 as Hyper369
import DASHI.Foundations.JPlusOneScaleBridge as JPlusOne

------------------------------------------------------------------------
-- Whole argument + level + provenance.
------------------------------------------------------------------------

record SituatedArgument
    (Whole Level Provenance : Set) : Set where
  constructor situatedArgument
  field
    wholeArgument : Whole
    currentLevel : Level
    provenance : Provenance

open SituatedArgument public

record LevelTransport
    {Whole Level Provenance : Set}
    (before after : SituatedArgument Whole Level Provenance) : Set where
  constructor levelTransport
  field
    wholeArgumentPreserved :
      wholeArgument before ≡ wholeArgument after
    provenancePreserved :
      provenance before ≡ provenance after

open LevelTransport public

identityLevelTransport :
  ∀ {Whole Level Provenance}
    {state : SituatedArgument Whole Level Provenance} →
  LevelTransport state state
identityLevelTransport = levelTransport refl refl

composeLevelTransport :
  ∀ {Whole Level Provenance}
    {a b c : SituatedArgument Whole Level Provenance} →
  LevelTransport a b →
  LevelTransport b c →
  LevelTransport a c
composeLevelTransport ab bc =
  levelTransport
    (trans (wholeArgumentPreserved ab) (wholeArgumentPreserved bc))
    (trans (provenancePreserved ab) (provenancePreserved bc))

------------------------------------------------------------------------
-- Local applicability is orthogonal to local support/counter-support.
------------------------------------------------------------------------

data Applicability : Set where
  applicableHere : Applicability
  noTypedMeetAtCurrentLevel : Applicability
  outsideCurrentComparisonScope : Applicability
  projectionCollapsedRequiredCoordinate : Applicability

record ArgumentStalk
    (Whole Level Provenance : Set) : Set where
  constructor argumentStalk
  field
    situated : SituatedArgument Whole Level Provenance
    evidence : Support.SupportSquare
    applicability : Applicability

open ArgumentStalk public

record StalkTransport
    {Whole Level Provenance : Set}
    (before after : ArgumentStalk Whole Level Provenance) : Set where
  constructor stalkTransport
  field
    carrierTransport :
      LevelTransport (situated before) (situated after)

open StalkTransport public

stalkTransportPreservesWholeArgument :
  ∀ {Whole Level Provenance}
    {before after : ArgumentStalk Whole Level Provenance} →
  StalkTransport before after →
  wholeArgument (situated before) ≡ wholeArgument (situated after)
stalkTransportPreservesWholeArgument transport =
  wholeArgumentPreserved (carrierTransport transport)

stalkTransportPreservesProvenance :
  ∀ {Whole Level Provenance}
    {before after : ArgumentStalk Whole Level Provenance} →
  StalkTransport before after →
  provenance (situated before) ≡ provenance (situated after)
stalkTransportPreservesProvenance transport =
  provenancePreserved (carrierTransport transport)

------------------------------------------------------------------------
-- Exact j -> j+1 rechart witness carrying the same argument/provenance.
------------------------------------------------------------------------

canonicalArgumentBefore :
  SituatedArgument String Chart.ChartIndex String
canonicalArgumentBefore =
  situatedArgument
    "whole argument retained across rechart"
    (Chart.chart 10)
    "source receipts + argument provenance"

canonicalArgumentAfter :
  SituatedArgument String Chart.ChartIndex String
canonicalArgumentAfter =
  situatedArgument
    "whole argument retained across rechart"
    (Chart.nextChart (Chart.chart 10))
    "source receipts + argument provenance"

canonicalArgumentJPlusOneTransport :
  LevelTransport canonicalArgumentBefore canonicalArgumentAfter
canonicalArgumentJPlusOneTransport = levelTransport refl refl

canonicalArgumentAfterIsChartEleven :
  currentLevel canonicalArgumentAfter ≡ Chart.chart 11
canonicalArgumentAfterIsChartEleven = refl

repoResidualRechartReachesChartEleven :
  Rechart.chart (Rechart.rechart Rechart.stateAtStar) ≡ Chart.chart 11
repoResidualRechartReachesChartEleven =
  Rechart.starRechartsToEleven

------------------------------------------------------------------------
-- Current-inspection failure is explicitly revisable without promotion.
------------------------------------------------------------------------

currentNoTypedMeetMayReviseByDeeperParse :
  Inspect.NoTypedMeetAtInspection.revisableUnderDeeperParse
    Inspect.canonicalNoTypedMeetAtCurrentInspection
  ≡ true
currentNoTypedMeetMayReviseByDeeperParse =
  Inspect.noTypedMeetAtCurrentInspectionMayReviseByDeeperParse

currentNoTypedMeetMayReviseByBridge :
  Inspect.NoTypedMeetAtInspection.revisableUnderBridge
    Inspect.canonicalNoTypedMeetAtCurrentInspection
  ≡ true
currentNoTypedMeetMayReviseByBridge =
  Inspect.noTypedMeetAtCurrentInspectionMayReviseByBridge

currentNoTypedMeetMayReviseByRoleAssignment :
  Inspect.NoTypedMeetAtInspection.revisableUnderNewRoleAssignment
    Inspect.canonicalNoTypedMeetAtCurrentInspection
  ≡ true
currentNoTypedMeetMayReviseByRoleAssignment =
  Inspect.noTypedMeetAtCurrentInspectionMayReviseByNewRoleAssignment

currentNoTypedMeetDoesNotPromoteTruth :
  Inspect.NoTypedMeetAtInspection.truthPromotion
    Inspect.canonicalNoTypedMeetAtCurrentInspection
  ≡ false
currentNoTypedMeetDoesNotPromoteTruth =
  Inspect.noTypedMeetAtCurrentInspectionNoTruthPromotion

------------------------------------------------------------------------
-- Same-fibre failure and scope-exceeded remain different residual situations.
------------------------------------------------------------------------

sameFibreNoTypedMeetIsNotScopeExceeded :
  Scope.NoTypedMeetComparedInFibre.ntmSixLevelResidual
    Scope.canonicalNoTypedMeetComparedInFibre
  ≡ Scope.Residual.noTypedMeet6
sameFibreNoTypedMeetIsNotScopeExceeded =
  Scope.canonicalNoTypedMeetRowIsNotScopeExceeded

outsideComparisonReallyIsScopeExceeded :
  Scope.ScopeExceededOutsideComparison.scopeSixLevelResidual
    Scope.canonicalScopeExceededOutsideComparison
  ≡ Scope.Residual.scopeExceeded6
outsideComparisonReallyIsScopeExceeded =
  Scope.canonicalScopeExceededRowResidualIsScopeExceeded

------------------------------------------------------------------------
-- Reopening / carry / 369 / J+1 exact cross-pollination receipts.
------------------------------------------------------------------------

projectionResidualDoesNotGrantSemanticErasure :
  Reopen.Quotient.ProjectionSemanticErasurePermission
    Reopen.Quotient.projectionReceiptOnly →
  ⊥
projectionResidualDoesNotGrantSemanticErasure =
  Reopen.Quotient.projectionReceiptCannotEraseSemantics

safeCarryReadsJAndJPlusOneTogether :
  Carry.depthEvaluationBoundary Carry.canonicalCarryMemorySubvoxelReceipt
  ≡ Carry.evaluateJAndJPlusOneTogether
safeCarryReadsJAndJPlusOneTogether =
  Carry.depthEvaluationBoundaryIsJAndJPlusOne
    Carry.canonicalCarryMemorySubvoxelReceipt

carryPreservesLowerResidueAsMemory :
  Carry.subvoxelMemory Carry.canonicalCarryMemorySubvoxelReceipt
  ≡ Carry.lowerResiduePersistsAsMemory
carryPreservesLowerResidueAsMemory =
  Carry.subvoxelMemoryPersists Carry.canonicalCarryMemorySubvoxelReceipt

nonaryIsNine : Hyper369.nonaryDimension ≡ 9
nonaryIsNine = Hyper369.nonaryDimensionIsNine

wovenTwoInteractionIsEightyOne :
  Hyper369.twoInteractionFabricDimension ≡ 81
wovenTwoInteractionIsEightyOne =
  Hyper369.twoInteractionFabricDimensionIsEightyOne

dialecticAtomIsTwentySeven :
  Hyper369.dialecticDiscussionAtomDimension ≡ 27
dialecticAtomIsTwentySeven =
  Hyper369.dialecticDiscussionAtomDimensionIsTwentySeven

stageAndMoonshineShareOnlyFreshUnitShape :
  JPlusOne.JPlusOneShapeAnalogy.commonCarrierPlusFreshUnitShape
    JPlusOne.canonicalJPlusOneShapeAnalogy
  ≡ true
stageAndMoonshineShareOnlyFreshUnitShape = refl

stageAndMoonshineValuesRemainDistinct :
  JPlusOne.JPlusOneShapeAnalogy.valuesIdentified
    JPlusOne.canonicalJPlusOneShapeAnalogy
  ≡ false
stageAndMoonshineValuesRemainDistinct = refl

stageAndMoonshineSemanticsRemainDistinct :
  JPlusOne.JPlusOneShapeAnalogy.semanticsIdentified
    JPlusOne.canonicalJPlusOneShapeAnalogy
  ≡ false
stageAndMoonshineSemanticsRemainDistinct = refl

------------------------------------------------------------------------
-- Argument obstruction is transport-local, not conclusion refutation.
------------------------------------------------------------------------

obstructionMayLeaveConclusionOpen :
  {core : Argument.ArgumentCore} →
  (obstruction : Argument.Obstruction core) →
  Bool
obstructionMayLeaveConclusionOpen =
  Argument.fallacyDoesNotRefuteConclusion

record ArgumentLevelTransportBoundary : Set where
  constructor argumentLevelTransportBoundary
  field
    localNoTypedMeetMeansGlobalFalsehood : Bool
    scopeExceededMeansArgumentErased : Bool
    projectionResidualMeansSemanticErasure : Bool
    jPlusOnePreservesWholeArgumentByConstruction : Bool
    residualMayTriggerRechart : Bool
    carryMemoryKeepsLowerLevelHistory : Bool
    twentySevenAddressesExhaustSemanticMeaning : Bool
    moonshineJEqualsChartJ : Bool

canonicalArgumentLevelTransportBoundary :
  ArgumentLevelTransportBoundary
canonicalArgumentLevelTransportBoundary =
  argumentLevelTransportBoundary
    false false false true true true false false
