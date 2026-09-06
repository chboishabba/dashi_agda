module DASHI.Cognition.PNF.SensibLawDutyHegemonyEpistemicCompressionV02Everything where

------------------------------------------------------------------------
-- DUTY / HEGEMONY / EPISTEMIC COMPRESSION / UNIVERSAL LAW V02
--
-- Preferred current-master capstone. It composes, but does not identify:
--   * doctrinal/legal derivability,
--   * observer adequacy,
--   * distributional/hegemony audit,
--   * relational/community authority,
--   * realised remedy.
--
-- No external claim is introduced here; source attribution remains in imported
-- owners (including Cullen [2026] HCA 19 and the Mabo/Pabai/Billy fixtures).
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawDutyHegemonyRelationalCrossPollinationEverything as Prior
import DASHI.Cognition.PNF.SensibLawUniversalLegalReopeningEverything as LegalReopen
import DASHI.Cognition.PNF.SensibLawLegalObserverResidualRefinementBidiExact as Residual
import DASHI.Cognition.PNF.SensibLawLegalGraphRefinementReopeningExact as Refinement
import DASHI.Cognition.PNF.SensibLawCullenPublicAuthorityDutyCalibrationExact as Cullen
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate
import DASHI.Cognition.PNF.SensibLawDoctrinalGateInterventionDistributionExact as Gate
import DASHI.Cognition.PNF.SensibLawRemedyUniversalLegalAlgebraBridgeExact as Remedy

------------------------------------------------------------------------
-- Existing jurisprudential firewalls remain live.
------------------------------------------------------------------------

noDutyStillDoesNotMeanNoIntervention : Gate.NoDutyMeansNoIntervention → ⊥
noDutyStillDoesNotMeanNoIntervention = Gate.noDutyIsNotNoIntervention

pabaiStillDoesNotCloseAllReformulations :
  Climate.PabaiNoDutyClosesEveryPossibleClimateDuty → ⊥
pabaiStillDoesNotCloseAllReformulations =
  Prior.pabaiNoDutyDoesNotCloseAllClimateReformulations

------------------------------------------------------------------------
-- Cullen is a discriminator against an accidental categorical public-authority
-- no-duty gate, not a donor of an automatic climate-duty conclusion.
------------------------------------------------------------------------

publicAuthorityNoDutyCannotBeCategorical :
  Cullen.PublicAuthorityFunctionCategoricallyPrecludesDuty → ⊥
publicAuthorityNoDutyCannotBeCategorical =
  Cullen.publicAuthorityIsNotCategoricalNoDuty

cullenDoesNotAutoPayClimateDuty :
  Cullen.CullenPoliceDutyAutomaticallyEstablishesClimateDuty → ⊥
cullenDoesNotAutoPayClimateDuty = Cullen.cullenDoesNotAutoCompileToClimateDuty

publicAuthorityResidualNeedsReasonInspection :
  Residual.preferredRoute
    (Residual.dutyResidualKind Climate.publicAuthorityFunction)
  ≡ Residual.inspectJudicialReasons
publicAuthorityResidualNeedsReasonInspection = refl

------------------------------------------------------------------------
-- Observer collision becomes a legal residual, not a rhetorical relabel.
------------------------------------------------------------------------

dutyStatutoryResidualNeedsStatutoryText :
  Residual.preferredRoute
    (Residual.dutyResidualKind Climate.statutoryCoherence)
  ≡ Residual.inspectStatutoryText
dutyStatutoryResidualNeedsStatutoryText = refl

dutyForeseeabilityResidualNeedsEvidence :
  Residual.preferredRoute
    (Residual.dutyResidualKind Climate.reasonableForeseeability)
  ≡ Residual.obtainFactualEvidence
dutyForeseeabilityResidualNeedsEvidence = refl

------------------------------------------------------------------------
-- A richer legal observer can reverse a prior conclusion through a newly
-- discovered exception/defeater. Provenance is append-only; conclusions are not.
------------------------------------------------------------------------

legalRefinementIsNotConclusionMonotone :
  Refinement.GraphExtensionPreservesEveryOldLegalConclusion → ⊥
legalRefinementIsNotConclusionMonotone =
  Refinement.graphExtensionIsNotConclusionMonotone

newFactsMayDefeatOldPath : Refinement.NewFactCanOnlyOpenAndNeverDefeat → ⊥
newFactsMayDefeatOldPath = Refinement.newFactsMayActivateExceptionsOrDefeaters

------------------------------------------------------------------------
-- Distributional/epistemic analysis does not manufacture legal authority, and
-- legal availability does not manufacture realised repair.
------------------------------------------------------------------------

data HegemonyAuditCreatesLegalAuthority : Set where
hegemonyAuditDoesNotCreateAuthority : HegemonyAuditCreatesLegalAuthority → ⊥
hegemonyAuditDoesNotCreateAuthority ()

legalAvailabilityStillDoesNotEqualRepair :
  Remedy.LegalAvailabilityAutomaticallyMeansRealisedRemedy → ⊥
legalAvailabilityStillDoesNotEqualRepair = Remedy.availabilityDoesNotEqualRealisation

------------------------------------------------------------------------
-- Aggregate boundary.
------------------------------------------------------------------------

data DutyHegemonyCompressionAggregateMeansKernelValidated : Set where
aggregateDoesNotClaimKernelValidation :
  DutyHegemonyCompressionAggregateMeansKernelValidated → ⊥
aggregateDoesNotClaimKernelValidation ()
