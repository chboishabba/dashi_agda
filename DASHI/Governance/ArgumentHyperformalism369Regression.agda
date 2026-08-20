module DASHI.Governance.ArgumentHyperformalism369Regression where

------------------------------------------------------------------------
-- Focused regression for the broad argument-level / 369 / J+1 tranche.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ArgumentLevelTransportHyperformalismExact as Transport
import DASHI.Core.LevelIndexedProofObligationHyperformalismExact as Levelled
import DASHI.Core.TypedProvenanceDependencyGraphExact as Graph
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Interop.JPlusOne369FibreCarryHyperformalismExact as Broad
import DASHI.Interop.CrossDomainLevelTransportRegression as CrossDomain
import DASHI.Interop.BroadMathProvenanceDependencyGraphExact as Provenance
import DASHI.Interop.PNFHyperfabric369 as H369
import DASHI.Foundations.JChartSuccessorBoundary as Chart
import DASHI.Foundations.JPlusOneScaleBridge as J1
import DASHI.Reasoning.CarryMemorySubvoxelReceipt as Carry
import DASHI.Physics.Closure.TeslaPolyphaseHistoricalBoundary as Tesla
import DASHI.Physics.Foundations.AtomicGenerationPipelineExact as Atomics
import DASHI.Biology.PedagogicalJPlusOneRouting as Pedagogy
import DASHI.Governance.ArgumentLevelAuthorityRoutingExact as Authority
import Moonshine as Moon

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
  ≡ Chart.chart 11
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
  NF.FactorsThrough Levelled.flattenEvidence Levelled.fineDecision → ⊥
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

nonaryNine : H369.nonaryDimension ≡ 9
nonaryNine = Broad.threeByThreeIsNine

dialecticAddressTwentySeven :
  H369.dialecticDiscussionAtomDimension ≡ 27
dialecticAddressTwentySeven = Broad.threeCubedAddressIsTwentySeven

wovenEightyOne : H369.twoInteractionFabricDimension ≡ 81
wovenEightyOne = Broad.nineSquaredIsEightyOne

mckayPlusOneExact : Moon.rep-dim + 1 ≡ Moon.j-coefficient
mckayPlusOneExact = Broad.mckayFreshUnitExact

carryReadsAdjacentDepths :
  Carry.depthEvaluationBoundary Carry.canonicalCarryMemorySubvoxelReceipt
  ≡ Carry.evaluateJAndJPlusOneTogether
carryReadsAdjacentDepths = Broad.carryRequiresJAndJPlusOneReading

lowerCarryResiduePersists :
  Carry.subvoxelMemory Carry.canonicalCarryMemorySubvoxelReceipt
  ≡ Carry.lowerResiduePersistsAsMemory
lowerCarryResiduePersists = Broad.lowerResiduePersistsAcrossCarry

moonshineAndChartJRemainDifferentCarriers :
  J1.JPlusOneShapeAnalogy.valuesIdentified J1.canonicalJPlusOneShapeAnalogy
  ≡ false
moonshineAndChartJRemainDifferentCarriers =
  Broad.sharedFreshUnitShapeDoesNotIdentifyValues

teslaUniversal369Blocked :
  Tesla.universal369DoctrinePromoted Tesla.teslaPolyphaseBoundary
  ≡ false
teslaUniversal369Blocked = Broad.teslaUniversal369NotPromoted

------------------------------------------------------------------------
-- Cross-domain adversarial instances.
------------------------------------------------------------------------

atomicOpenStagesRemainVisible :
  Atomics.generatorAuthority Atomics.enumerateNuclearCharges
    ≡ Atomics.stageFiniteAnalogue
  ×
  Atomics.generatorAuthority Atomics.solveDeclaredHamiltonian
    ≡ Atomics.stageExternallyOpen
atomicOpenStagesRemainVisible =
  CrossDomain.atomicEnumerationDoesNotSolveHamiltonian

pedagogicalPlusOneNotAutomatic :
  Pedagogy.jPlusOneNotAutomatic Pedagogy.canonicalPedagogicalJPlusOneRouting
  ≡ true
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
  Attr.atlasCreatesAuthority Provenance.canonicalBroadSourceAtlas ≡ false
sourceAtlasDoesNotCreateAuthority =
  Provenance.canonicalBroadSourceAtlasDoesNotCreateAuthority
