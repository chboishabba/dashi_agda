module DASHI.Base369Plus54ProofFabricValidation where

open import DASHI.Core.Prelude

import DASHI.Algebra.Trit as Trit
import DASHI.Biology.JFineCoarseRelativeScaleExact as JScale
import DASHI.Foundations.Base369Completion54SituatedTriadBridgeExact as Completion
import DASHI.Foundations.Base369SharedNonaryIdentityTransportExact as SharedJ
import DASHI.Foundations.Base369StableAlgebraicIdentityTowerExact as Stable
import DASHI.Foundations.Base369MonsterNamedIdentityRegistryExact as Registry
import DASHI.Foundations.Base369JCoarseFineStableIdentityDisciplineExact as JIdentity
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata
import DASHI.Combinatorics.TextileDependencyGrammarProcessExact as Process
import DASHI.Combinatorics.ProofFabricLocalCompatibilityExact as Local
import DASHI.Combinatorics.ProofFabricCompilerExact as Fabric
import DASHI.Culture.IntellectualReceptionSituatedInformationParetoPreorderExact as Pareto
import Base369 as Base

coarseNinePlusOneRegression :
  Completion.coarseBaseChannels + Completion.coarseCompletionChannels
  ≡ Completion.coarseCarrierChannels
coarseNinePlusOneRegression = Completion.coarseNinePlusOne

coarseBulkRegression :
  Completion.baseBulk + Completion.completionBulk ≡ Completion.coarseBulk
coarseBulkRegression = Completion.coarseBulkDecomposesNinePlusOne

situatedTwoByThreeRegression : 2 * 3 ≡ Completion.situatedSlotCount
situatedTwoByThreeRegression = Completion.twoRowsTimesThreeColumns

comparisonNineRegression : 3 * 3 ≡ Completion.comparisonSheetCount
comparisonNineRegression = Completion.threeTimesThreeIsNine

localCompletion54Regression :
  Completion.situatedSlotCount * Completion.comparisonSheetCount
  ≡ Completion.localCompletionCount
localCompletion54Regression = Completion.sixTimesNineIs54

localResidual53Regression :
  1 + Completion.localResidualCount ≡ Completion.localCompletionCount
localResidual53Regression = Completion.onePlusResidualIs54

base27Times729Regression :
  Completion.base27Count * Completion.ternarySituatedValuationCount
  ≡ Completion.globalFineFibre
base27Times729Regression = Completion.baseTimesAppraisalIsFineFibre

sharedJIsNineRegression : SharedJ.sharedJ ≡ 9
sharedJIsNineRegression = SharedJ.sharedJIsNine

sharedJLocalResolutionRegression : SharedJ.resolveJ SharedJ.localSituatedBoundary ≡ 54
sharedJLocalResolutionRegression = SharedJ.localBoundaryViaJIs54

sharedJGlobalResolutionRegression : SharedJ.resolveJ SharedJ.globalPointedFineBulk ≡ 196830
sharedJGlobalResolutionRegression = SharedJ.globalPointedViaJIs196830

fiftyFourIsTwo27CellsRegression : 2 * 27 ≡ 54
fiftyFourIsTwo27CellsRegression = SharedJ.fiftyFourIsTwoTimesTwentySeven

monsterBulkIsFive54Times729Regression :
  5 * 54 * 729 ≡ SharedJ.globalPointedViaJ
monsterBulkIsFive54Times729Regression = SharedJ.monsterBulkIsFiveTimes54Times729

fiftyFourTimes3645Regression :
  54 * SharedJ.fiveTimes729 ≡ SharedJ.globalPointedViaJ
fiftyFourTimes3645Regression = SharedJ.fiftyFourTimes3645IsMonsterBulk

bothHaveNineFactorLocalRegression :
  SharedJ.sharedJ * 6 ≡ SharedJ.localBoundaryViaJ
bothHaveNineFactorLocalRegression = SharedJ.localAsNineTimesSix

bothHaveNineFactorGlobalRegression :
  SharedJ.sharedJ * 21870 ≡ SharedJ.globalPointedViaJ
bothHaveNineFactorGlobalRegression = SharedJ.globalAsNineTimes21870

stable54CarrierIsoRegression :
  Stable.CarrierIso
    Stable.Completion54
    (Completion.SituatedTriadRow × Stable.Base27)
stable54CarrierIsoRegression = Stable.completion54IsTwoBy27

stable10CarrierIsoRegression :
  Stable.CarrierIso
    Stable.Pointed10
    (Stable.FiveMode × Stable.Orientation2)
stable10CarrierIsoRegression = Stable.pointed10IsFiveByTwo

stable196830CarrierIsoRegression :
  Stable.CarrierIso
    Stable.MonsterBulk196830
    Stable.BulkFive54Appraisal
stable196830CarrierIsoRegression = Stable.monsterBulkIsFiveBy54By729

namedDecision27Regression :
  Stable.CarrierIso Stable.Base27 Registry.DecisionCondition27
namedDecision27Regression = Registry.decision27IsBase27

namedMonsterStateRegression :
  Stable.CarrierIso
    Stable.BulkFive54Appraisal
    Registry.NamedMonsterDecisionState196830
namedMonsterStateRegression = Registry.namedMonsterDecisionIso

cornerEightRegression : Registry.cornerCarrierCount ≡ 8
cornerEightRegression = refl

cornerEightMatchesVoxelRegression :
  Registry.cornerCarrierCount ≡ Strata.cornerCount
cornerEightMatchesVoxelRegression = Registry.cornerCountAgreesWithExistingStratum

jCoarseCountRegression : JScale.jCoarseFrequency ≡ 9
jCoarseCountRegression = JIdentity.jCoarseCountPinned

jFineCountRegression : JScale.jFineFrequency ≡ 19683
jFineCountRegression = JIdentity.jFineCountPinned

binaryLiftDoesNotProduceMidRegression :
  (level : Pareto.AxisLevel) →
  Completion.axisLevelToTri level ≡ Base.tri-mid → ⊥
binaryLiftDoesNotProduceMidRegression = Completion.binaryProfileNeverIntroducesMid

proofReservedTileRejectedRegression :
  Local.LocallyWellTypedTile Fabric.tile11 → ⊥
proofReservedTileRejectedRegression = Local.reservedTileCannotType

proofCompiledStreamTypedRegression :
  (stream : List Trit.Trit) →
  Local.LocallyCompatibleFabric (Fabric.compileTritStream stream)
proofCompiledStreamTypedRegression = Local.compiledTritStreamLocallyCompatible

completionBoundaryRegression : Completion.Base369Completion54SituatedTriadBoundary
completionBoundaryRegression = Completion.canonicalBase369Completion54SituatedTriadBoundary

sharedNonaryBoundaryRegression : SharedJ.Base369SharedNonaryIdentityBoundary
sharedNonaryBoundaryRegression = SharedJ.canonicalBase369SharedNonaryIdentityBoundary

stableIdentityBoundaryRegression : Stable.StableAlgebraicIdentityBoundary
stableIdentityBoundaryRegression = Stable.canonicalStableAlgebraicIdentityBoundary

namedIdentityBoundaryRegression : Registry.NamedMonsterMeaningBoundary
namedIdentityBoundaryRegression = Registry.canonicalNamedMonsterMeaningBoundary

jIdentityBoundaryRegression : JIdentity.JCoarseFineIdentityBoundary
jIdentityBoundaryRegression = JIdentity.canonicalJCoarseFineIdentityBoundary

processBoundaryRegression : Process.TextileDependencyGrammarProcessBoundary
processBoundaryRegression = Process.canonicalTextileDependencyGrammarProcessBoundary

proofFabricLocalBoundaryRegression : Local.ProofFabricLocalCompatibilityBoundary
proofFabricLocalBoundaryRegression = Local.canonicalProofFabricLocalCompatibilityBoundary
