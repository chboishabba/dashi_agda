module DASHI.Governance.DecisionContestedAuthorityJusticeConvergenceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Cognition.PNF.DecisionActionProjectionNonFactorabilityExact as DecisionProjection
import DASHI.Cognition.PNF.DecisionAutonomyExact as Autonomy
import DASHI.Governance.ContestedAmbientAuthorityHyperformalismExact as Ambient
import DASHI.Governance.InstitutionPreservingRechartAntiSublationExact as Rechart
import DASHI.Governance.LegalDecisionDoubleProjectionExact as Legal
import DASHI.Governance.PeaceJusticeResidualNonFactorabilityExact as PeaceJustice
import DASHI.Ontology.ProgenitorParentAuthorityRoutingNonfactorabilityExact as ParentAuthority
open import DASHI.Ontology.ProgenitorParentProjectionFibre

------------------------------------------------------------------------
-- DECISION x CONTESTED AUTHORITY x JUSTICE CONVERGENCE
--
-- One institutional surface can be compatible with different hidden decision
-- history, autonomy, authority provenance and justice residual.  This composes
-- the #606 decision/action fibre with the #603 contested-authority/justice
-- owners; neither stack is redefined here.
------------------------------------------------------------------------

record InstitutionalEpisode : Set where
  constructor institutionalEpisode
  field
    legalEpisode : Legal.LegalDecisionEpisode
    autonomyEpisode : Autonomy.ActionEpisode
    politicalState : Rechart.PoliticalFineState

open InstitutionalEpisode public

InstitutionalSurface : Set
InstitutionalSurface =
  Legal.OfficialSurface × Autonomy.ExecutedAction × Rechart.OrderObservation
  where
    open import DASHI.Cognition.PNF.UnifiedDecisionDynamicsExact using (ExecutedAction)

institutionalSurface : InstitutionalEpisode → InstitutionalSurface
institutionalSurface episode =
  Legal.officialSurface (legalEpisode episode)
  , (Autonomy.emitted (autonomyEpisode episode)
  , Rechart.orderObserver (politicalState episode))

record FineInstitutionalState : Set where
  constructor fineInstitutionalState
  field
    hiddenDecision : DecisionProjection.FineDecisionState
    hiddenAuthority : ParentAuthority.ParentAuthorityRoute
    hiddenAutonomy : Autonomy.AutonomyAxes
    hiddenJusticeResidual : PeaceJustice.JusticeResidualStatus

open FineInstitutionalState public

fineInstitutionalStateOf : InstitutionalEpisode → FineInstitutionalState
fineInstitutionalStateOf episode =
  fineInstitutionalState
    (DecisionProjection.fineDecisionState
      (Legal.decisionEpisode (legalEpisode episode)))
    (ParentAuthority.routeParentAuthority
      (Legal.legalRelation (legalEpisode episode)))
    (Autonomy.axes (autonomyEpisode episode))
    (PeaceJustice.justiceResidual (politicalState episode))

unresolvedAdoptive : Legal.LegalDecisionEpisode
unresolvedAdoptive =
  Legal.legalDecisionEpisode
    DecisionProjection.unresolvedInaction
    adoptiveCarrier

fineJustEpisode : InstitutionalEpisode
fineJustEpisode =
  institutionalEpisode
    Legal.blockedDonor
    Autonomy.autonomousWithdrawal
    Rechart.justQuietState

collapsedOpenEpisode : InstitutionalEpisode
collapsedOpenEpisode =
  institutionalEpisode
    unresolvedAdoptive
    Autonomy.constrainedWithdrawal
    Rechart.suppressedQuietState

sameInstitutionalSurface :
  institutionalSurface fineJustEpisode
  ≡ institutionalSurface collapsedOpenEpisode
sameInstitutionalSurface = refl

decisionHistoryDiffers :
  hiddenDecision (fineInstitutionalStateOf fineJustEpisode)
  ≡ hiddenDecision (fineInstitutionalStateOf collapsedOpenEpisode) → ⊥
decisionHistoryDiffers = DecisionProjection.blockedAndUnresolvedDifferFineState

authorityRouteDiffers :
  hiddenAuthority (fineInstitutionalStateOf fineJustEpisode)
  ≡ hiddenAuthority (fineInstitutionalStateOf collapsedOpenEpisode) → ⊥
authorityRouteDiffers = ParentAuthority.routesDiffer

autonomyDiffers :
  hiddenAutonomy (fineInstitutionalStateOf fineJustEpisode)
  ≡ hiddenAutonomy (fineInstitutionalStateOf collapsedOpenEpisode) → ⊥
autonomyDiffers equality with
  cong Autonomy.relevantAlternativesAccessible equality
... | ()

justiceResidualDiffers :
  hiddenJusticeResidual (fineInstitutionalStateOf fineJustEpisode)
  ≡ hiddenJusticeResidual (fineInstitutionalStateOf collapsedOpenEpisode) → ⊥
justiceResidualDiffers ()

fineInstitutionalStatesDiffer :
  fineInstitutionalStateOf fineJustEpisode
  ≡ fineInstitutionalStateOf collapsedOpenEpisode → ⊥
fineInstitutionalStatesDiffer equality =
  decisionHistoryDiffers (cong hiddenDecision equality)

institutionalSurfaceNonfactorability :
  NF.NonFactorabilityWitness institutionalSurface fineInstitutionalStateOf
institutionalSurfaceNonfactorability =
  NF.nonFactorabilityWitness
    fineJustEpisode
    collapsedOpenEpisode
    sameInstitutionalSurface
    fineInstitutionalStatesDiffer

institutionalSurfaceCannotRecoverFineState :
  NF.FactorsThrough institutionalSurface fineInstitutionalStateOf → ⊥
institutionalSurfaceCannotRecoverFineState =
  NF.witnessRulesOutEveryFlatFactorisation institutionalSurfaceNonfactorability

institutionalClosureDoesNotEstablishJusticeClosure :
  PeaceJustice.JusticeClosureCertificate Rechart.suppressedQuietState → ⊥
institutionalClosureDoesNotEstablishJusticeClosure =
  PeaceJustice.orderOnlyPeaceDoesNotEstablishJusticeClosure

coerciveAmbientClaimStillDoesNotSelfLegitimate :
  Ambient.LegitimateAmbientAuthority Ambient.forceDominantAmbientClaim → _
coerciveAmbientClaimStillDoesNotSelfLegitimate =
  Ambient.coerciveDominanceDoesNotEstablishLegitimateAmbientAuthority

record DecisionContestedAuthorityJusticeBoundary : Set where
  constructor decisionContestedAuthorityJusticeBoundary
  field
    sameInstitutionalSurfaceDeterminesDecisionHistory : Bool
    sameInstitutionalSurfaceDeterminesAutonomy : Bool
    sameInstitutionalSurfaceDeterminesAuthorityRoute : Bool
    sameInstitutionalSurfaceDeterminesJusticeResidual : Bool
    institutionalClosureCreatesJusticeClosure : Bool
    coerciveDominanceCreatesLegitimateAmbientAuthority : Bool

canonicalDecisionContestedAuthorityJusticeBoundary :
  DecisionContestedAuthorityJusticeBoundary
canonicalDecisionContestedAuthorityJusticeBoundary =
  decisionContestedAuthorityJusticeBoundary false false false false false false
