module DASHI.Governance.ArgumentHyperformalism369Regression where

------------------------------------------------------------------------
-- Focused regression for the broad argument-level / 369 / J+1 tranche.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ArgumentLevelTransportHyperformalismExact as Transport
import DASHI.Core.LevelIndexedProofObligationHyperformalismExact as Levelled
import DASHI.Core.TypedProvenanceDependencyGraphExact as Graph
import DASHI.Interop.JPlusOne369FibreCarryHyperformalismExact as Broad
import DASHI.Interop.CrossDomainLevelTransportRegression as CrossDomain
import DASHI.Interop.BroadMathProvenanceDependencyGraphExact as Provenance
import DASHI.Governance.ArgumentLevelAuthorityRoutingExact as Authority

------------------------------------------------------------------------
-- Whole argument / provenance survive level transport.
------------------------------------------------------------------------

argumentJPlusOneKeepsWhole :
  Transport.wholeArgument Transport.canonicalArgumentBefore
  ≡ Transport.wholeArgument Transport.canonicalArgumentAfter
argumentJPlusOneKeepsWhole =
  Transport.wholeArgumentPreserved
    Transport.canonicalArgumentJPlusOneTransport

argumentJPlusOneKeepsProvenance :
  Transport.provenance Transport.canonicalArgumentBefore
  ≡ Transport.provenance Transport.canonicalArgumentAfter
argumentJPlusOneKeepsProvenance =
  Transport.provenancePreserved
    Transport.canonicalArgumentJPlusOneTransport

argumentRechartsToEleven :
  Transport.currentLevel Transport.canonicalArgumentAfter
  ≡ Transport.Chart.chart 11
argumentRechartsToEleven =
  Transport.canonicalArgumentAfterIsChartEleven

------------------------------------------------------------------------
-- Local evidence cannot reconstruct applicability/level-aware routing.
------------------------------------------------------------------------

sameSupportDifferentApplicability :
  Levelled.evidence Levelled.positiveApplicable
  ≡ Levelled.evidence Levelled.positiveOutOfScope
sameSupportDifferentApplicability =
  Levelled.sameEvidenceDifferentApplicability

flatSupportCannotRecoverLevelAwareDecision :
  Levelled.NF.FactorsThrough Levelled.flattenEvidence Levelled.fineDecision → ⊥
flatSupportCannotRecoverLevelAwareDecision =
  Levelled.noFlatEvidenceFactorisationRecoversLevelAwareDecision

authorityLevelShiftKeepsClaim :
  Levelled.claim (Levelled.coordinate Authority.intakeCurrentAuthorityStalk)
  ≡ Levelled.claim (Levelled.coordinate Authority.reviewCurrentAuthorityStalk)
authorityLevelShiftKeepsClaim = Authority.authorityReviewKeepsClaim

authorityLevelShiftKeepsProvenance :
  Levelled.provenance (Levelled.coordinate Authority.intakeCurrentAuthorityStalk)
  ≡ Levelled.provenance (Levelled.coordinate Authority.reviewCurrentAuthorityStalk)
authorityLevelShiftKeepsProvenance = Authority.authorityReviewKeepsProvenance

------------------------------------------------------------------------
-- Broad 369/J+1/carry/Moonshine arithmetic and boundaries.
------------------------------------------------------------------------

nonaryNine : Broad.H369.nonaryDimension ≡ 9
nonaryNine = Broad.threeByThreeIsNine

dialecticAddressTwentySeven :
  Broad.H369.dialecticDiscussionAtomDimension ≡ 27
dialecticAddressTwentySeven = Broad.threeCubedAddressIsTwentySeven

wovenEightyOne : Broad.H369.twoInteractionFabricDimension ≡ 81
wovenEightyOne = Broad.nineSquaredIsEightyOne

mckayPlusOneExact : Broad.Moon.rep-dim + 1 ≡ Broad.Moon.j-coefficient
mckayPlusOneExact = Broad.mckayFreshUnitExact

carryReadsAdjacentDepths :
  Broad.Carry.depthEvaluationBoundary Broad.Carry.canonicalCarryMemorySubvoxelReceipt
  ≡ Broad.Carry.evaluateJAndJPlusOneTogether
carryReadsAdjacentDepths = Broad.carryRequiresJAndJPlusOneReading

lowerCarryResiduePersists :
  Broad.Carry.subvoxelMemory Broad.Carry.canonicalCarryMemorySubvoxelReceipt
  ≡ Broad.Carry.lowerResiduePersistsAsMemory
lowerCarryResiduePersists = Broad.lowerResiduePersistsAcrossCarry

moonshineAndChartJRemainDifferentCarriers :
  Broad.J1.JPlusOneShapeAnalogy.valuesIdentified Broad.J1.canonicalJPlusOneShapeAnalogy
  ≡ false
moonshineAndChartJRemainDifferentCarriers =
  Broad.sharedFreshUnitShapeDoesNotIdentifyValues

teslaUniversal369Blocked :
  Broad.Tesla.universal369DoctrinePromoted Broad.Tesla.teslaPolyphaseBoundary
  ≡ false
teslaUniversal369Blocked = Broad.teslaUniversal369NotPromoted

------------------------------------------------------------------------
-- Cross-domain adversarial instances.
------------------------------------------------------------------------

atomicOpenStagesRemainVisible =
  CrossDomain.atomicEnumerationDoesNotSolveHamiltonian

pedagogicalPlusOneNotAutomatic =
  CrossDomain.pedagogicalJPlusOneIsNotAutomatic

------------------------------------------------------------------------
-- Dependency infographic contract.
------------------------------------------------------------------------

boundedGraphHasThirteenNodes :
  Graph.totalNodes Provenance.canonicalBroadLoad ≡ 13
boundedGraphHasThirteenNodes = Provenance.canonicalBroadTotalNodesIsThirteen

boundedGraphHasElevenTypedEdges :
  Graph.totalEdges Provenance.canonicalBroadLoad ≡ 11
boundedGraphHasElevenTypedEdges = Provenance.canonicalBroadTotalEdgesIsEleven

boundedGraphDashiCountIsSix :
  Graph.dashiNodes Provenance.canonicalBroadLoad ≡ 6
boundedGraphDashiCountIsSix = Provenance.canonicalBroadDashiNodesIsSix

sourceAtlasDoesNotCreateAuthority :
  Provenance.Attr.atlasCreatesAuthority Provenance.canonicalBroadSourceAtlas ≡ false
sourceAtlasDoesNotCreateAuthority =
  Provenance.canonicalBroadSourceAtlasDoesNotCreateAuthority
