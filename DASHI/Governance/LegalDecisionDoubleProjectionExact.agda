module DASHI.Governance.LegalDecisionDoubleProjectionExact where

------------------------------------------------------------------------
-- LEGAL DECISION DOUBLE PROJECTION
--
-- Cross-pollination of the decision/action fibre with the already-merged
-- parent/authority routing fibre.  The intended shape is:
--
--   fine decision episode × fine legal relation
--      -> expressed action × fine legal relation
--      -> official action × public legal slot.
--
-- The first projection can erase decision-state/autonomy distinctions.  The
-- second can erase authority-routing distinctions.  Their composite therefore
-- cannot reconstruct either class of hidden state merely from the official
-- surface.
--
-- This is a finite structural theorem.  It does not classify a live person's
-- autonomy, a live family relation, or the legality/justice of an actual case.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.NonFactorabilityCompositionExact as Composition
import DASHI.Cognition.PNF.DecisionActionProjectionNonFactorabilityExact as DecisionProjection
import DASHI.Cognition.PNF.DecisionAutonomyExact as Autonomy
import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact as Decision
import DASHI.Ontology.ProgenitorParentAuthorityRoutingNonfactorabilityExact as ParentAuthority
open import DASHI.Ontology.ProgenitorParentHyperfabric using (WikidataParentSlot)
open import DASHI.Ontology.ProgenitorParentProjectionFibre

------------------------------------------------------------------------
-- 1. Coupled fine carrier and the two observational stages.
------------------------------------------------------------------------

record LegalDecisionEpisode : Set where
  constructor legalDecisionEpisode
  field
    decisionEpisode : DecisionProjection.DecisionEpisode
    legalRelation : ParentCarrier

open LegalDecisionEpisode public

ExpressedSurface : Set
ExpressedSurface = Decision.ExecutedAction × ParentCarrier

OfficialSurface : Set
OfficialSurface = Decision.ExecutedAction × WikidataParentSlot

expressedSurface : LegalDecisionEpisode → ExpressedSurface
expressedSurface episode =
  DecisionProjection.observedAction (decisionEpisode episode)
  , legalRelation episode

institutionalProjection : ExpressedSurface → OfficialSurface
institutionalProjection expressed =
  proj₁ expressed , projectParentSlot (proj₂ expressed)

officialSurface : LegalDecisionEpisode → OfficialSurface
officialSurface =
  Composition.TwoStageProjection expressedSurface institutionalProjection

record FineLegalState : Set where
  constructor fineLegalState
  field
    hiddenDecisionState : DecisionProjection.FineDecisionState
    currentAuthorityRoute : ParentAuthority.ParentAuthorityRoute

open FineLegalState public

fineLegalStateOf : LegalDecisionEpisode → FineLegalState
fineLegalStateOf episode =
  fineLegalState
    (DecisionProjection.fineDecisionState (decisionEpisode episode))
    (ParentAuthority.routeParentAuthority (legalRelation episode))

------------------------------------------------------------------------
-- 2. First-stage loss: same expression, different decision state.
------------------------------------------------------------------------

blockedDonor unresolvedDonor blockedAdoptive : LegalDecisionEpisode
blockedDonor =
  legalDecisionEpisode
    DecisionProjection.blockedCommitment
    anonymousDonorCarrier
unresolvedDonor =
  legalDecisionEpisode
    DecisionProjection.unresolvedInaction
    anonymousDonorCarrier
blockedAdoptive =
  legalDecisionEpisode
    DecisionProjection.blockedCommitment
    adoptiveCarrier

blockedAndUnresolvedShareExpression :
  expressedSurface blockedDonor ≡ expressedSurface unresolvedDonor
blockedAndUnresolvedShareExpression = refl

blockedAndUnresolvedFineLegalStateDiffer :
  fineLegalStateOf blockedDonor ≡ fineLegalStateOf unresolvedDonor → ⊥
blockedAndUnresolvedFineLegalStateDiffer equality =
  DecisionProjection.blockedAndUnresolvedDifferFineState
    (cong hiddenDecisionState equality)

expressionDecisionLossWitness :
  NF.NonFactorabilityWitness expressedSurface fineLegalStateOf
expressionDecisionLossWitness =
  NF.nonFactorabilityWitness
    blockedDonor
    unresolvedDonor
    blockedAndUnresolvedShareExpression
    blockedAndUnresolvedFineLegalStateDiffer

-- Further institutional coarsening cannot repair the decision distinction that
-- was already erased at expression.
officialSurfaceStillLosesDecisionState :
  NF.NonFactorabilityWitness officialSurface fineLegalStateOf
officialSurfaceStillLosesDecisionState =
  Composition.postcomposeNonFactorability
    institutionalProjection
    expressionDecisionLossWitness

------------------------------------------------------------------------
-- 3. Second-stage loss: same official slot, different authority route.
------------------------------------------------------------------------

blockedDonorAndAdoptiveShareOfficialSurface :
  officialSurface blockedDonor ≡ officialSurface blockedAdoptive
blockedDonorAndAdoptiveShareOfficialSurface = refl

blockedDonorAndAdoptiveAuthorityDiffer :
  fineLegalStateOf blockedDonor ≡ fineLegalStateOf blockedAdoptive → ⊥
blockedDonorAndAdoptiveAuthorityDiffer equality =
  ParentAuthority.routesDiffer
    (cong currentAuthorityRoute equality)

officialAuthorityLossWitness :
  NF.NonFactorabilityWitness officialSurface fineLegalStateOf
officialAuthorityLossWitness =
  NF.nonFactorabilityWitness
    blockedDonor
    blockedAdoptive
    blockedDonorAndAdoptiveShareOfficialSurface
    blockedDonorAndAdoptiveAuthorityDiffer

officialSurfaceCannotRecoverFineLegalState :
  NF.FactorsThrough officialSurface fineLegalStateOf → ⊥
officialSurfaceCannotRecoverFineLegalState =
  NF.witnessRulesOutEveryFlatFactorisation
    officialAuthorityLossWitness

------------------------------------------------------------------------
-- 4. Autonomy is independently hidden by the same official action surface.
------------------------------------------------------------------------

record LegalAutonomyEpisode : Set where
  constructor legalAutonomyEpisode
  field
    autonomyEpisode : Autonomy.ActionEpisode
    autonomyLegalRelation : ParentCarrier

open LegalAutonomyEpisode public

AutonomyOfficialSurface : Set
AutonomyOfficialSurface = Decision.ExecutedAction × WikidataParentSlot

autonomyOfficialSurface : LegalAutonomyEpisode → AutonomyOfficialSurface
autonomyOfficialSurface episode =
  Autonomy.emitted (autonomyEpisode episode)
  , projectParentSlot (autonomyLegalRelation episode)

record FineAutonomyLegalState : Set where
  constructor fineAutonomyLegalState
  field
    hiddenAutonomyAxes : Autonomy.AutonomyAxes
    hiddenAutonomyAuthorityRoute : ParentAuthority.ParentAuthorityRoute

open FineAutonomyLegalState public

fineAutonomyLegalStateOf : LegalAutonomyEpisode → FineAutonomyLegalState
fineAutonomyLegalStateOf episode =
  fineAutonomyLegalState
    (Autonomy.axes (autonomyEpisode episode))
    (ParentAuthority.routeParentAuthority (autonomyLegalRelation episode))

autonomousDonor constrainedDonor : LegalAutonomyEpisode
autonomousDonor =
  legalAutonomyEpisode Autonomy.autonomousWithdrawal anonymousDonorCarrier
constrainedDonor =
  legalAutonomyEpisode Autonomy.constrainedWithdrawal anonymousDonorCarrier

autonomousAndConstrainedShareOfficialSurface :
  autonomyOfficialSurface autonomousDonor
  ≡ autonomyOfficialSurface constrainedDonor
autonomousAndConstrainedShareOfficialSurface = refl

autonomyAxesDiffer :
  Autonomy.freeAxes ≡ Autonomy.constrainedAxes → ⊥
autonomyAxesDiffer equality with
  cong Autonomy.relevantAlternativesAccessible equality
... | ()

autonomousAndConstrainedFineStateDiffer :
  fineAutonomyLegalStateOf autonomousDonor
  ≡ fineAutonomyLegalStateOf constrainedDonor → ⊥
autonomousAndConstrainedFineStateDiffer equality =
  autonomyAxesDiffer (cong hiddenAutonomyAxes equality)

officialAutonomyLossWitness :
  NF.NonFactorabilityWitness
    autonomyOfficialSurface
    fineAutonomyLegalStateOf
officialAutonomyLossWitness =
  NF.nonFactorabilityWitness
    autonomousDonor
    constrainedDonor
    autonomousAndConstrainedShareOfficialSurface
    autonomousAndConstrainedFineStateDiffer

officialActionCannotRecoverAutonomyAndAuthority :
  NF.FactorsThrough autonomyOfficialSurface fineAutonomyLegalStateOf → ⊥
officialActionCannotRecoverAutonomyAndAuthority =
  NF.witnessRulesOutEveryFlatFactorisation officialAutonomyLossWitness

------------------------------------------------------------------------
-- 5. Decision-history and authority are transverse residual coordinates.
--
-- Adding only one residual to the official surface still leaves a collision on
-- the other.  Adding their typed join is sufficient for the deliberately
-- chosen FineLegalState consumer.  This is not whole-episode reconstruction.
------------------------------------------------------------------------

DecisionResidualSurface : Set
DecisionResidualSurface = OfficialSurface × DecisionProjection.FineDecisionState

AuthorityResidualSurface : Set
AuthorityResidualSurface = OfficialSurface × ParentAuthority.ParentAuthorityRoute

JoinedResidualSurface : Set
JoinedResidualSurface = OfficialSurface × FineLegalState

decisionResidualSurface : LegalDecisionEpisode → DecisionResidualSurface
decisionResidualSurface episode =
  officialSurface episode
  , DecisionProjection.fineDecisionState (decisionEpisode episode)

authorityResidualSurface : LegalDecisionEpisode → AuthorityResidualSurface
authorityResidualSurface episode =
  officialSurface episode
  , ParentAuthority.routeParentAuthority (legalRelation episode)

joinedResidualSurface : LegalDecisionEpisode → JoinedResidualSurface
joinedResidualSurface episode = officialSurface episode , fineLegalStateOf episode

decisionResidualStillCollapsesAuthority :
  decisionResidualSurface blockedDonor
  ≡ decisionResidualSurface blockedAdoptive
decisionResidualStillCollapsesAuthority = refl

decisionResidualAuthorityLossWitness :
  NF.NonFactorabilityWitness decisionResidualSurface fineLegalStateOf
decisionResidualAuthorityLossWitness =
  NF.nonFactorabilityWitness
    blockedDonor
    blockedAdoptive
    decisionResidualStillCollapsesAuthority
    blockedDonorAndAdoptiveAuthorityDiffer

authorityResidualStillCollapsesDecisionHistory :
  authorityResidualSurface blockedDonor
  ≡ authorityResidualSurface unresolvedDonor
authorityResidualStillCollapsesDecisionHistory = refl

authorityResidualDecisionLossWitness :
  NF.NonFactorabilityWitness authorityResidualSurface fineLegalStateOf
authorityResidualDecisionLossWitness =
  NF.nonFactorabilityWitness
    blockedDonor
    unresolvedDonor
    authorityResidualStillCollapsesDecisionHistory
    blockedAndUnresolvedFineLegalStateDiffer

decisionResidualAloneCannotRecoverFineLegalState :
  NF.FactorsThrough decisionResidualSurface fineLegalStateOf → ⊥
decisionResidualAloneCannotRecoverFineLegalState =
  NF.witnessRulesOutEveryFlatFactorisation
    decisionResidualAuthorityLossWitness

authorityResidualAloneCannotRecoverFineLegalState :
  NF.FactorsThrough authorityResidualSurface fineLegalStateOf → ⊥
authorityResidualAloneCannotRecoverFineLegalState =
  NF.witnessRulesOutEveryFlatFactorisation
    authorityResidualDecisionLossWitness

joinedResidualRecoversChosenFineLegalState :
  NF.FactorsThrough joinedResidualSurface fineLegalStateOf
joinedResidualRecoversChosenFineLegalState =
  NF.factorsThrough proj₂ (λ episode → refl)

------------------------------------------------------------------------
-- 6. Consolidated boundary.
------------------------------------------------------------------------

record LegalDecisionProjectionBoundary : Set where
  constructor legalDecisionProjectionBoundary
  field
    sameExpressionCanHideDifferentDecisionState : Bool
    laterInstitutionalProjectionRepairsEarlierLoss : Bool
    sameOfficialSurfaceCanHideDifferentAuthorityRoute : Bool
    sameOfficialActionCanHideDifferentAutonomyState : Bool
    eitherResidualAloneIsSufficient : Bool
    joinedResidualIsSufficientForChosenFineState : Bool
    officialSurfaceEqualsFineLegalState : Bool

canonicalLegalDecisionProjectionBoundary : LegalDecisionProjectionBoundary
canonicalLegalDecisionProjectionBoundary =
  legalDecisionProjectionBoundary
    true false true true false true false
