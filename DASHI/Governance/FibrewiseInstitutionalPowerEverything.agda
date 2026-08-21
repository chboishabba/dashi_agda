module DASHI.Governance.FibrewiseInstitutionalPowerEverything where

------------------------------------------------------------------------
-- Focused aggregate for the full conversation-derived formalism.
-- This file intentionally owns no parallel mathematics: it imports the
-- theorem-bearing components and exposes a compact regression boundary.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Governance.AuthorityMandateCore as Authority
import DASHI.Governance.ContestedAmbientAuthorityHyperformalismExact as Ambient
import DASHI.Governance.EpistemicCaptureProfessionalClosureExact as Capture
import DASHI.Governance.EpistemicErrorAllocationChillingBridgeExact as ErrorAllocation
import DASHI.Governance.InstitutionPreservingRechartAntiSublationExact as Rechart
import DASHI.Governance.InstitutionalNoticeActuationCulpabilityExact as Notice
import DASHI.Governance.OppositionInterfaceAntiDomesticationExact as Opposition

------------------------------------------------------------------------
-- Direct regression aliases: if an upstream owner changes incompatibly this
-- aggregate should stop typechecking rather than silently weakening the model.
------------------------------------------------------------------------

regressionInterfaceDoesNotExhaustIndependentSource :
  Ambient.LeftExhaustive Ambient.canonicalPartialInterface → ⊥
regressionInterfaceDoesNotExhaustIndependentSource =
  Ambient.recognitionInterfaceDoesNotExhaustSourceCarrier

regressionCoerciveDominanceDoesNotSelfLegitimate :
  Ambient.LegitimateAmbientAuthority Ambient.forceDominantAmbientClaim →
  Authority.Never
regressionCoerciveDominanceDoesNotSelfLegitimate =
  Ambient.coerciveDominanceDoesNotEstablishLegitimateAmbientAuthority

regressionLayFibreNotDecisionSafe : Notice.DecisionSafe Notice.layObserver → ⊥
regressionLayFibreNotDecisionSafe = Notice.layObserverIsNotDecisionSafe

regressionDiagnosticStillNotClosed :
  Notice.EffectiveNotice Notice.diagnosticObserver → ⊥
regressionDiagnosticStillNotClosed =
  Notice.diagnosticInteractionIsNotYetEffectiveNotice

regressionAIActuationWithoutRefinement : Notice.ActuationWithoutRefinement
regressionAIActuationWithoutRefinement = Notice.canonicalActuationWithoutRefinement

regressionSavingBranchPairwiseParetoLiveAfterAI : Notice.PairwiseParetoLiveAfterAI
regressionSavingBranchPairwiseParetoLiveAfterAI =
  Notice.savingBranchBecomesPairwiseParetoLiveAfterAI

regressionLayPersistenceNotPromotedToCulpability :
  Notice.CostsCulpable Notice.layObserver → ⊥
regressionLayPersistenceNotPromotedToCulpability =
  Notice.layPersistenceCannotBePromotedToThisCulpabilityBoundary

regressionFormalEqualityCapabilityGap : Notice.FormalEqualityCapabilityGap
regressionFormalEqualityCapabilityGap = Notice.canonicalFormalEqualityCapabilityGap

regressionAuthoritySurfaceCollision :
  Observer.Separating Capture.formalSurfaceObserver → ⊥
regressionAuthoritySurfaceCollision = Capture.authoritySurfaceIsNotSeparating

regressionProductionClosureMigratesToValidation :
  Capture.ProfessionalClosureMigrationWitness
regressionProductionClosureMigratesToValidation =
  Capture.canonicalProfessionalClosureMigration

regressionExteriorCannotBeConsumedByAdmissionInterface :
  Capture.PubliclyAdmitted
    Capture.canonicalRepresentationBoundRegime
    Ambient.sourceExterior → ⊥
regressionExteriorCannotBeConsumedByAdmissionInterface =
  Capture.exteriorCannotBeAdmittedByRepresentationBoundRegime

regressionHostObstructionDoesNotRefuteExternalValidity :
  Rechart.ExternalValiditySurvivesHostObstruction
regressionHostObstructionDoesNotRefuteExternalValidity =
  Rechart.hostObstructionDoesNotRefuteExternalValidity

regressionHistoricalDerivationNotCurrentJustification :
  Rechart.GenealogyJustificationSeparationWitness
regressionHistoricalDerivationNotCurrentJustification =
  Rechart.canonicalGenealogyJustificationSeparation

regressionQuietSurfaceDoesNotDetermineJustice :
  Rechart.orderObserver Rechart.justQuietState
    ≡ Rechart.orderObserver Rechart.suppressedQuietState
  × (Rechart.justiceObserver Rechart.justQuietState
      ≡ Rechart.justiceObserver Rechart.suppressedQuietState → ⊥)
regressionQuietSurfaceDoesNotDetermineJustice =
  Rechart.quietSurfaceDoesNotDetermineJustice

regressionAdmittedOppositionDoesNotExhaustPoliticalCarrier :
  Ambient.LeftExhaustive Opposition.oppositionAdministrativeInterface → ⊥
regressionAdmittedOppositionDoesNotExhaustPoliticalCarrier =
  Opposition.oppositionInterfaceIsNotExhaustive

regressionVisiblePluralityCanShareAdmissionRule :
  Opposition.VisiblePluralitySharedSkeleton
regressionVisiblePluralityCanShareAdmissionRule =
  Opposition.canonicalVisiblePluralitySharedSkeleton

regressionEpistemicErrorAllocationIsAChoice :
  ErrorAllocation.EpistemicErrorAllocationWitness
regressionEpistemicErrorAllocationIsAChoice =
  ErrorAllocation.canonicalEpistemicErrorAllocationWitness

regressionSanctionLearningIsNotFineRuleLearning :
  ErrorAllocation.sanctionLearningOutcome
    ≡ ErrorAllocation.closureLearningOutcome → ⊥
regressionSanctionLearningIsNotFineRuleLearning =
  ErrorAllocation.avoidanceIsNotFineRuleLearning

------------------------------------------------------------------------
-- Compact all-up boundary.
------------------------------------------------------------------------

record FibrewiseInstitutionalPowerBoundary : Set where
  constructor fibrewiseInstitutionalPowerBoundary
  field
    oneAmbientCarrierByConstruction : Bool
    noTypedMeetAnnihilatesExternalState : Bool
    recognitionExhaustsSource : Bool
    coercionCreatesAuthority : Bool
    polishedSurfaceCreatesValidity : Bool
    cheapActuationCreatesFineObserver : Bool
    repeatedNoticeCreatesDecisionSafety : Bool
    diagnosticInteractionCreatesClosure : Bool
    culpabilityPrecedesDecisionSafeClosure : Bool
    formalEqualityCreatesCapabilityEquality : Bool
    internalSkeletonBindsExternalCarrier : Bool
    orderSurfaceCreatesJusticeClosure : Bool
    admittedOppositionImpliesMetaRulePower : Bool
    visiblePluralityImpliesOpenAdmissionAlgebra : Bool
    comprehensionFailureDeterminesFaultAllocation : Bool
    sanctionAutomaticallyTeachesFineRule : Bool
    residualAndExteriorMustRemainReopenableOrPresent : Bool

canonicalFibrewiseInstitutionalPowerBoundary : FibrewiseInstitutionalPowerBoundary
canonicalFibrewiseInstitutionalPowerBoundary =
  fibrewiseInstitutionalPowerBoundary
    false false false false false false false false false false false false
    false false false false true
