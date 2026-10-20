module DASHI.Governance.BoloBoloIncidenceCompressionExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt

------------------------------------------------------------------------
-- IDEALISED INCIDENCE-COMPRESSION SCENARIOS.
--
-- This owner isolates the purely combinatorial gain that motivates the cost
-- comparison.  Suppose there are k equal local communities, each with n
-- participants and q issues that are genuinely local to that community.
--
-- Counterfactual globally-coupled routing:
--   every one of k*n participants is coupled to every one of k*q issues.
--
-- Subsidiary/local routing:
--   each community's n participants are coupled only to its q local issues.
--
-- Therefore the two counts are represented by:
--   global = (k*n) * (k*q)
--   local  = k * (n*q)
--
-- This is DASHI combinatorial modelling.  It is not a claim that real social
-- cost is linear in edge count, nor a formula stated by p.m.
------------------------------------------------------------------------

record EqualPartitionIncidenceScenario : Set where
  constructor equalPartitionIncidenceScenario
  field
    communityCount : Nat
    participantsPerCommunity : Nat
    localIssuesPerCommunity : Nat

open EqualPartitionIncidenceScenario public

globalIncidenceEdges : EqualPartitionIncidenceScenario → Nat
globalIncidenceEdges scenario =
  (communityCount scenario * participantsPerCommunity scenario)
  * (communityCount scenario * localIssuesPerCommunity scenario)

localIncidenceEdges : EqualPartitionIncidenceScenario → Nat
localIncidenceEdges scenario =
  communityCount scenario
  * (participantsPerCommunity scenario * localIssuesPerCommunity scenario)

------------------------------------------------------------------------
-- Source-inspired arithmetic scenarios.
--
-- The community counts / approximate populations are taken from the already
-- source-bounded bolo'bolo atlas, but the one-local-issue-per-unit scenario and
-- the globally-coupled comparison are DASHI assumptions introduced solely to
-- expose topology.  These numbers are not observations of real bolos.
------------------------------------------------------------------------

kanaLowerScenario : EqualPartitionIncidenceScenario
kanaLowerScenario = equalPartitionIncidenceScenario 20 15 1

kanaUpperScenario : EqualPartitionIncidenceScenario
kanaUpperScenario = equalPartitionIncidenceScenario 20 30 1

tegaTenBoloScenario : EqualPartitionIncidenceScenario
tegaTenBoloScenario = equalPartitionIncidenceScenario 10 500 1

tegaTwentyBoloScenario : EqualPartitionIncidenceScenario
tegaTwentyBoloScenario = equalPartitionIncidenceScenario 20 500 1

kanaLowerCompressionIdentity :
  globalIncidenceEdges kanaLowerScenario
  ≡ 20 * localIncidenceEdges kanaLowerScenario
kanaLowerCompressionIdentity = refl

kanaUpperCompressionIdentity :
  globalIncidenceEdges kanaUpperScenario
  ≡ 20 * localIncidenceEdges kanaUpperScenario
kanaUpperCompressionIdentity = refl

tegaTenCompressionIdentity :
  globalIncidenceEdges tegaTenBoloScenario
  ≡ 10 * localIncidenceEdges tegaTenBoloScenario
tegaTenCompressionIdentity = refl

tegaTwentyCompressionIdentity :
  globalIncidenceEdges tegaTwentyBoloScenario
  ≡ 20 * localIncidenceEdges tegaTwentyBoloScenario
tegaTwentyCompressionIdentity = refl

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record IncidenceCompressionBoundary : Set where
  constructor incidenceCompressionBoundary
  field
    equalPartitionScenarioIsDASHIDerived : Bool
    oneIssuePerCommunityIsSourceClaim : Bool
    globalAllToAllRoutingIsSourceClaim : Bool
    quadraticIncidenceFormulaAttributedToPM : Bool
    combinatorialScenarioIsEmpiricalScalingLaw : Bool
    incidenceEdgeReductionDefinitionallyEqualsCostReduction : Bool
    localityCanReducePotentialCouplingUnderScenario : Bool
    federationBoundaryOverheadStillMustBeAdded : Bool
    heterogeneousCommunitySizesRemainPossible : Bool
    crossCommunityIssuesRemainPossible : Bool

open IncidenceCompressionBoundary public

canonicalIncidenceCompressionBoundary : IncidenceCompressionBoundary
canonicalIncidenceCompressionBoundary =
  incidenceCompressionBoundary
    true
    false
    false
    false
    false
    false
    true
    true
    true
    true

canonicalBoloIncidenceCompressionReceipt : GenericReceipt.GenericReceipt
canonicalBoloIncidenceCompressionReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo idealised incidence-compression scenarios"
    "DASHI.Governance.BoloBoloIncidenceCompressionExact"
    "kana/tega compression identities / canonicalIncidenceCompressionBoundary"
    "makes the topology gain explicit in an idealised equal-partition model: globally coupling every local issue produces (k*n)*(k*q) potential participant-issue incidences, while subsidiary routing produces k*(n*q); source-inspired 20-kana and 10/20-bolo examples therefore expose 20x and 10/20x incidence-count contrasts under the stated one-local-issue assumptions"
    "the equal partition, one-issue, and all-to-all counterfactual assumptions are DASHI-derived rather than p.m. claims; incidence count is not coordination cost, real systems may be heterogeneous and cross-community issues/federation overhead must still be measured"
    "agda -i . DASHI/Governance/BoloBoloIncidenceCompressionRegression.agda"
