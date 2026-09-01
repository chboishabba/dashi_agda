module DASHI.Culture.IntellectualReceptionStratifiedStabiliserSearchAuthorityFibreExact where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ProofSearchLeastPrivilegeAdmissionExact as ProofSearch
import DASHI.Culture.IntellectualReceptionAdmissibilityStratumWhatIfExact as Reception
import DASHI.Culture.IntellectualReceptionContextIndexedAuthorisedStabiliserProofSearchExperimentExact as Context
import DASHI.Culture.IntellectualReceptionContextAuthorisationSequentialExperimentExact as Sequential
import DASHI.Culture.IntellectualReceptionSemanticStabiliserParetoAuthorityCrossPollinationExact as Stabiliser
import DASHI.Core.AdmissibleConsumerMDLHyperfabricExact as MDL
import DASHI.Moonshine.Base369Ternary27StratifiedFibreHolonomyExact as Base369Stratified

------------------------------------------------------------------------
-- STRATIFIED STABILISER SEARCH / AUTHORITY FIBRE
--
-- The earlier reception owner defines a stratum as more than a coarse label:
-- present surface + arrival history + topology + gate + next move + future cone.
-- This file keeps that discipline.  A semantic generator does not progress
-- through one scalar ladder from "candidate" to "authorised".  Proof-search
-- investigability and governance authority are separate fine coordinates over
-- a shared coarse semantic/reception surface.
------------------------------------------------------------------------

data StabiliserFineState : Set where
  baselineReflectionFibre
  reviewedReflectionFibre
  : StabiliserFineState

data CoarseSemanticStratum : Set where
  comparisonReflectionSemanticStratum : CoarseSemanticStratum

data SearchFibreCode : Set where
  admittedInvestigation : SearchFibreCode

data GovernanceGateCode : Set where
  authorityPending authorityOpen : GovernanceGateCode

data StabiliserNextMove : Set where
  inspectAuthorityResidual
  rankEligibleReflection
  enactAuthorisedReflection
  : StabiliserNextMove

data StabiliserFutureCone : Set where
  investigationCone
  eligibleRankingCone
  : StabiliserFutureCone

coarseSemanticStratum : StabiliserFineState → CoarseSemanticStratum
coarseSemanticStratum _ = comparisonReflectionSemanticStratum

searchFibre : StabiliserFineState → SearchFibreCode
searchFibre _ = admittedInvestigation

governanceGate : StabiliserFineState → GovernanceGateCode
governanceGate baselineReflectionFibre = authorityPending
governanceGate reviewedReflectionFibre = authorityOpen

nextMove : StabiliserFineState → StabiliserNextMove
nextMove baselineReflectionFibre = inspectAuthorityResidual
nextMove reviewedReflectionFibre = rankEligibleReflection

futureCone : StabiliserFineState → StabiliserFutureCone
futureCone baselineReflectionFibre = investigationCone
futureCone reviewedReflectionFibre = eligibleRankingCone

------------------------------------------------------------------------
-- Both fine states retain the same underlying reception stratum and same
-- semantic generator.  The authority/search fibre is additional structure;
-- reception history is not replaced by it.
------------------------------------------------------------------------

receptionSurface : StabiliserFineState → Reception.ReceptionAdmissibilityStratum
receptionSurface _ = Reception.commentaryPluralStratum

generatorSurface : StabiliserFineState → Stabiliser.GeometricGenerator
generatorSurface _ = Stabiliser.comparisonFlipXGenerator

sameReceptionStratumAcrossAuthorityContexts :
  receptionSurface baselineReflectionFibre
  ≡ receptionSurface reviewedReflectionFibre
sameReceptionStratumAcrossAuthorityContexts = refl

sameGeneratorAcrossAuthorityContexts :
  generatorSurface baselineReflectionFibre
  ≡ generatorSurface reviewedReflectionFibre
sameGeneratorAcrossAuthorityContexts = refl

sameCoarseSemanticStratumAcrossAuthorityContexts :
  coarseSemanticStratum baselineReflectionFibre
  ≡ coarseSemanticStratum reviewedReflectionFibre
sameCoarseSemanticStratumAcrossAuthorityContexts = refl

sameSearchFibreAcrossAuthorityContexts :
  searchFibre baselineReflectionFibre
  ≡ searchFibre reviewedReflectionFibre
sameSearchFibreAcrossAuthorityContexts = refl

------------------------------------------------------------------------
-- Exact proof-bearing coordinates.
------------------------------------------------------------------------

semanticLawfulAtBaseline :
  Stabiliser.SemanticRolePreservingGenerator
    (generatorSurface baselineReflectionFibre)
semanticLawfulAtBaseline = Stabiliser.semanticComparisonReflection

semanticLawfulAtReviewed :
  Stabiliser.SemanticRolePreservingGenerator
    (generatorSurface reviewedReflectionFibre)
semanticLawfulAtReviewed = Stabiliser.semanticComparisonReflection

proofSearchLiveAtBaseline : ProofSearch.LiveProofSearch
proofSearchLiveAtBaseline = Context.comparisonReflectionInvestigationIsLive

baselineGovernanceStillBlocked :
  Context.ContextAuthorisedGenerator
    Context.baselineAuthorityContext
    Stabiliser.comparisonFlipXGenerator → ⊥
baselineGovernanceStillBlocked =
  Context.baselineComparisonReflectionNotAuthorised

reviewedGovernanceOpen :
  Context.ContextAuthorisedGenerator
    Context.reviewedComparisonContext
    Stabiliser.comparisonFlipXGenerator
reviewedGovernanceOpen = Context.reviewedComparisonReflectionAuthorised

reviewedEligibilityOpen :
  MDL.Eligible
    (Context.contextEligibilityProblem Context.reviewedComparisonContext)
    Stabiliser.comparisonFlipXGenerator
reviewedEligibilityOpen = Context.reviewedComparisonReflectionEligible

baselineEligibilityBlocked :
  MDL.Eligible
    (Context.contextEligibilityProblem Context.baselineAuthorityContext)
    Stabiliser.comparisonFlipXGenerator → ⊥
baselineEligibilityBlocked = Context.baselineComparisonReflectionNotEligible

------------------------------------------------------------------------
-- Same coarse stratum and same proof-search status do not recover governance
-- gate, next admissible move, or future cone.
------------------------------------------------------------------------

governanceGatesDiffer :
  governanceGate baselineReflectionFibre
  ≡ governanceGate reviewedReflectionFibre → ⊥
governanceGatesDiffer ()

nextMovesDiffer :
  nextMove baselineReflectionFibre
  ≡ nextMove reviewedReflectionFibre → ⊥
nextMovesDiffer ()

futureConesDiffer :
  futureCone baselineReflectionFibre
  ≡ futureCone reviewedReflectionFibre → ⊥
futureConesDiffer ()

coarseSemanticStratumCannotRecoverGovernanceGate :
  INF.FactorsThrough coarseSemanticStratum governanceGate → ⊥
coarseSemanticStratumCannotRecoverGovernanceGate =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      baselineReflectionFibre
      reviewedReflectionFibre
      refl
      governanceGatesDiffer)

coarseSemanticStratumCannotRecoverFutureCone :
  INF.FactorsThrough coarseSemanticStratum futureCone → ⊥
coarseSemanticStratumCannotRecoverFutureCone =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      baselineReflectionFibre
      reviewedReflectionFibre
      refl
      futureConesDiffer)

searchFibreCannotRecoverGovernanceGate :
  INF.FactorsThrough searchFibre governanceGate → ⊥
searchFibreCannotRecoverGovernanceGate =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      baselineReflectionFibre
      reviewedReflectionFibre
      refl
      governanceGatesDiffer)

searchFibreCannotRecoverFutureCone :
  INF.FactorsThrough searchFibre futureCone → ⊥
searchFibreCannotRecoverFutureCone =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      baselineReflectionFibre
      reviewedReflectionFibre
      refl
      futureConesDiffer)

------------------------------------------------------------------------
-- Proof-relevant move enablement.  This is deliberately not a probability.
------------------------------------------------------------------------

data EnabledMove : StabiliserFineState → StabiliserNextMove → Set where
  inspectWhilePending :
    EnabledMove baselineReflectionFibre inspectAuthorityResidual
  rankWhenAuthorised :
    EnabledMove reviewedReflectionFibre rankEligibleReflection
  enactWhenAuthorised :
    Context.ContextAuthorisedGenerator
      Context.reviewedComparisonContext
      Stabiliser.comparisonFlipXGenerator →
    EnabledMove reviewedReflectionFibre enactAuthorisedReflection

baselineCannotRankAsEligible :
  EnabledMove baselineReflectionFibre rankEligibleReflection → ⊥
baselineCannotRankAsEligible ()

baselineCannotEnactAuthorisedReflection :
  EnabledMove baselineReflectionFibre enactAuthorisedReflection → ⊥
baselineCannotEnactAuthorisedReflection ()

reviewedCanEnactAuthorisedReflection :
  EnabledMove reviewedReflectionFibre enactAuthorisedReflection
reviewedCanEnactAuthorisedReflection =
  enactWhenAuthorised reviewedGovernanceOpen

------------------------------------------------------------------------
-- Sequential proof-search/experiment is attached only to the pending fibre.
-- Its output may close the declared authority consumer, but the governance
-- receipt remains an independent fine coordinate.
------------------------------------------------------------------------

pendingAuthorityExperiment :
  Sequential.InvestigableBeforeAuthorised
pendingAuthorityExperiment = Sequential.canonicalInvestigableBeforeAuthorised

------------------------------------------------------------------------
-- Structural precedent from the now-merged Base369 stratified-fibre owner:
-- same coarse stratum need not recover a fine endpoint/transport order.  This
-- theorem is consumed only as a non-collapse precedent; no identification of
-- the reception fibre with the Base369 fabric is asserted.
------------------------------------------------------------------------

base369SameStratumStillDoesNotRecoverTransportOrder :
  Base369Stratified.FactorsTransportOrderThroughStratum → ⊥
base369SameStratumStillDoesNotRecoverTransportOrder =
  Base369Stratified.stratumCannotRecoverTransportOrder

data ReceptionStabiliserFibreIsLiteralBase369Fibre : Set where
data SearchStratumIsGovernanceAuthority : Set where
data GovernanceGateIsSemanticMeaning : Set where
data FutureConeIsHistoricalFact : Set where

receptionStabiliserFibreIsNotLiteralBase369Fibre :
  ReceptionStabiliserFibreIsLiteralBase369Fibre → ⊥
receptionStabiliserFibreIsNotLiteralBase369Fibre ()

searchStratumDoesNotCreateGovernanceAuthority :
  SearchStratumIsGovernanceAuthority → ⊥
searchStratumDoesNotCreateGovernanceAuthority ()

governanceGateDoesNotDefineSemanticMeaning :
  GovernanceGateIsSemanticMeaning → ⊥
governanceGateDoesNotDefineSemanticMeaning ()

futureConeIsNotAssertedHistoricalFact :
  FutureConeIsHistoricalFact → ⊥
futureConeIsNotAssertedHistoricalFact ()

record IntellectualReceptionStratifiedStabiliserSearchAuthorityBoundary : Set where
  constructor intellectual-reception-stratified-stabiliser-search-authority-boundary
  field
    sameSemanticStratumCanHideDifferentGovernanceGate : Bool
    sameSearchStatusCanHideDifferentGovernanceGate : Bool
    sameSemanticStratumCanHideDifferentFutureCone : Bool
    proofSearchInvestigabilityEqualsGovernanceAuthority : Bool
    governanceAuthorityDefinesSemanticMeaning : Bool
    disabledMoveMeansLowProbability : Bool
    reviewedAuthorityCanExpandEnabledMoveCone : Bool
    receptionFibreIsLiteralBase369Fibre : Bool
    futureConeIsAssertedHistory : Bool
    sourceAttributionBoundarySurvives : Bool

canonicalIntellectualReceptionStratifiedStabiliserSearchAuthorityBoundary :
  IntellectualReceptionStratifiedStabiliserSearchAuthorityBoundary
canonicalIntellectualReceptionStratifiedStabiliserSearchAuthorityBoundary =
  intellectual-reception-stratified-stabiliser-search-authority-boundary
    true true true false false false true false false true
