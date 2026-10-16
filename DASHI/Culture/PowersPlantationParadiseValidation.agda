module DASHI.Culture.PowersPlantationParadiseValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.RequiredObserverAxisJoinAdequacyExact as Join
import DASHI.Governance.AsymmetricLegibilityContestabilityExact as Legibility
import DASHI.Culture.PowersPlantationParadiseSynthesisExact as Synthesis
import DASHI.Culture.ColonialPerformanceStatusNonfactorabilityExact as Performance
import DASHI.Culture.HistoricalArchiveAbsenceNonfactorabilityExact as Archive
import DASHI.Culture.ColonialTheatreAccessAdapterExact as Access
import DASHI.Culture.PowersPlantationParadiseGovernedCrossPollinationExact as Cross
import DASHI.Culture.PowersPlantationParadiseEmpiricalProgrammeExact as Empirical
import DASHI.Culture.PowersPlantationParadiseEmpiricalAcquisitionParetoExact as EmpiricalPareto
import DASHI.Culture.PowersPlantationParadiseMinetteMicrohistoryExact as Minette
import DASHI.Culture.PowersPlantationParadiseMinetteChronologyContestationExact as MinetteChronology
import DASHI.Culture.PowersPlantationParadiseEnslavedDistributionEvidenceExact as EnslavedEvidence
import DASHI.Culture.PowersPlantationParadisePerformerComparisonExact as PerformerComparison
import DASHI.Culture.PowersPlantationParadiseComparativeVenueEvidenceExact as ComparativeVenue
import DASHI.Culture.PowersPlantationParadiseEmpiricalPhase3Validation as Phase3
import DASHI.Culture.PowersPlantationParadiseEmpiricalRoadmapExact as Roadmap
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesNarrativeGovernanceWeldExact as Rooted

_paradise-material-gap-paid : INF.FactorsThrough Synthesis.paradiseObserver Synthesis.materialAffordance → ⊥
_paradise-material-gap-paid = Synthesis.paradiseObserverCannotRecoverMaterialAffordance

_performance-status-gap-paid : INF.FactorsThrough Performance.performedRole Performance.socialOccupancy → ⊥
_performance-status-gap-paid = Performance.performedRoleCannotRecoverSocialOccupancy

_performance-endorsement-gap-paid : INF.FactorsThrough Performance.performanceSurface Performance.endorsement → ⊥
_performance-endorsement-gap-paid = Performance.performanceCannotRecoverEndorsement

_archive-absence-gap-paid : INF.FactorsThrough Archive.archiveObservation Archive.worldPresence → ⊥
_archive-absence-gap-paid = Archive.absenceInArchiveCannotRecoverAbsenceInWorld

_access-gap-paid : INF.FactorsThrough Access.productionSurface Access.venueAccessClass → ⊥
_access-gap-paid = Access.sameProductionCannotRecoverVenueAccess

_local-expansion-global-emancipation-gap-paid : INF.FactorsThrough Synthesis.localExpansion Synthesis.globalEmancipation → ⊥
_local-expansion-global-emancipation-gap-paid = Synthesis.localExpansionDoesNotProveGlobalEmancipation

_governed-standing-gap-paid : INF.FactorsThrough Cross.culturalSurface Cross.standingCode → ⊥
_governed-standing-gap-paid = Cross.sameCulturalSurfaceCannotRecoverStanding

_contestability-gap-paid : INF.FactorsThrough Cross.culturalSurface Cross.contestabilityCode → ⊥
_contestability-gap-paid = Cross.sameCulturalSurfaceCannotRecoverContestability

_material-cone-gap-paid : INF.FactorsThrough Cross.culturalSurface Cross.materialConeCode → ⊥
_material-cone-gap-paid = Cross.sameCulturalSurfaceCannotRecoverMaterialCone

_joint-required-axes-gap-paid : Join.RetainsBothRequiredAxes Cross.culturalSurface Cross.standingCode Cross.contestabilityCode → ⊥
_joint-required-axes-gap-paid = Cross.sameCulturalSurfaceCannotRetainStandingAndContestability

_governed-social-position-gap-paid : INF.FactorsThrough Cross.culturalSurface Cross.governedSocialPositionJoint → ⊥
_governed-social-position-gap-paid = Cross.sameCulturalSurfaceCannotRetainGovernedSocialPosition

_legibility-decoder-gap-paid : Legibility.ExactInstitutionalViewDecoder Cross.powersLegibilityChannel → ⊥
_legibility-decoder-gap-paid = Cross.powersExactInstitutionalViewDecoderImpossible

_empirical-minette-receipt-paid : Empirical.SameObjectEmpiricalReceipt
_empirical-minette-receipt-paid = Empirical.minetteCareerStatusReceipt

_empirical-seating-receipt-paid : Empirical.SameObjectEmpiricalReceipt
_empirical-seating-receipt-paid = Empirical.portAuPrinceSeatingGeometryReceipt

_empirical-causal-firewall-paid : Empirical.ObservationalEvidenceIdentifiesCausalEffect → ⊥
_empirical-causal-firewall-paid = Empirical.observationalEvidenceDoesNotIdentifyCausalEffect

_empirical-acquisition-frontier-paid :
  EmpiricalPareto.empiricalAcquisitionFrontier
  ≡ EmpiricalPareto.primaryCorpusCell ∷ EmpiricalPareto.distributionalIncidenceCell ∷ []
_empirical-acquisition-frontier-paid = EmpiricalPareto.currentFrontierIsCorpusDistribution

_benefit-does-not-prove-settlement-paid : Minette.BenefitPerformancePaysSettlement → ⊥
_benefit-does-not-prove-settlement-paid = Minette.benefitPerformanceDoesNotProveSettlement

_minette-salary-nonpayment-paid : Minette.MinetteSalaryNonpaymentReceipt
_minette-salary-nonpayment-paid = Minette.minette1784SalaryNonpaymentReceipt

_secondary-date-disagreement-needs-primary-paid : Minette.SecondaryDateDisagreementResolvedWithoutPrimaryInspection → ⊥
_secondary-date-disagreement-needs-primary-paid = Minette.secondaryDateDisagreementNeedsPrimaryInspection

_minette-date-contestation-paid : MinetteChronology.minette1790NoticeContestationRelation ≡ MinetteChronology.minette1790NoticeContestationRelation
_minette-date-contestation-paid = refl

_enslaved-distribution-category-evidence-paid : EnslavedEvidence.EnslavedTheatreDistributionEvidence
_enslaved-distribution-category-evidence-paid = EnslavedEvidence.prest2023DistributionEvidence

_julien-contribution-burden-paid : EnslavedEvidence.EnslavedMusicianContributionBurdenReceipt
_julien-contribution-burden-paid = EnslavedEvidence.julien1781ContributionBurdenReceipt

_lise-saint-marc-event-paid : PerformerComparison.PerformerEventReceipt
_lise-saint-marc-event-paid = PerformerComparison.liseSaintMarc1786Receipt

_sibling-comparison-not-causal-control-paid : PerformerComparison.SiblingComparisonPaysCausalCounterfactual → ⊥
_sibling-comparison-not-causal-control-paid = PerformerComparison.siblingComparisonDoesNotPayCausalCounterfactual

_martinique-comparative-seating-paid : ComparativeVenue.ComparativeVenueReceipt
_martinique-comparative-seating-paid = ComparativeVenue.saintPierre1786PlannedSeatingReceipt

_martinique-not-saint-domingue-rule-paid : ComparativeVenue.MartiniqueEvidenceTransportsSaintDomingueRule → ⊥
_martinique-not-saint-domingue-rule-paid = ComparativeVenue.martiniqueEvidenceDoesNotTransportSaintDomingueRule

_phase3-validation-reachable : Roadmap.PowersEmpiricalRoadmapBoundary
_phase3-validation-reachable = Phase3.roadmapBoundary

_roadmap-boundary-paid : Roadmap.PowersEmpiricalRoadmapBoundary
_roadmap-boundary-paid = Roadmap.canonicalPowersEmpiricalRoadmapBoundary

_rooted-trace-paid : Rooted.RootedTraceClaim Cross.powersChapter5Root Cross.powersChapter5Leaf
_rooted-trace-paid = Cross.powersChapter5RootedTraceClaim

_source-theorem-firewall-paid : Synthesis.powersSourceClaim ≡ Synthesis.dashiTheorem → ⊥
_source-theorem-firewall-paid = Synthesis.sourceClaimDoesNotBecomeDASHITheorem
