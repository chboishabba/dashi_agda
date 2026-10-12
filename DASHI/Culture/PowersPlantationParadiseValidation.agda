module DASHI.Culture.PowersPlantationParadiseValidation where

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.PowersPlantationParadiseSynthesisExact as Synthesis
import DASHI.Culture.ColonialPerformanceStatusNonfactorabilityExact as Performance
import DASHI.Culture.HistoricalArchiveAbsenceNonfactorabilityExact as Archive
import DASHI.Culture.ColonialTheatreAccessAdapterExact as Access
import DASHI.Culture.PowersPlantationParadiseGovernedCrossPollinationExact as Cross
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesNarrativeGovernanceWeldExact as Rooted

------------------------------------------------------------------------
-- Focused compile-time validation / regression surface.
------------------------------------------------------------------------

_paradise-material-gap-paid :
  INF.FactorsThrough Synthesis.paradiseObserver Synthesis.materialAffordance → ⊥
_paradise-material-gap-paid =
  Synthesis.paradiseObserverCannotRecoverMaterialAffordance

_performance-status-gap-paid :
  INF.FactorsThrough Performance.performedRole Performance.socialOccupancy → ⊥
_performance-status-gap-paid =
  Performance.performedRoleCannotRecoverSocialOccupancy

_performance-endorsement-gap-paid :
  INF.FactorsThrough Performance.performanceSurface Performance.endorsement → ⊥
_performance-endorsement-gap-paid =
  Performance.performanceCannotRecoverEndorsement

_archive-absence-gap-paid :
  INF.FactorsThrough Archive.archiveObservation Archive.worldPresence → ⊥
_archive-absence-gap-paid =
  Archive.absenceInArchiveCannotRecoverAbsenceInWorld

_access-gap-paid :
  INF.FactorsThrough Access.productionSurface Access.venueAccessClass → ⊥
_access-gap-paid =
  Access.sameProductionCannotRecoverVenueAccess

_local-expansion-global-emancipation-gap-paid :
  INF.FactorsThrough Synthesis.localExpansion Synthesis.globalEmancipation → ⊥
_local-expansion-global-emancipation-gap-paid =
  Synthesis.localExpansionDoesNotProveGlobalEmancipation

_governed-standing-gap-paid :
  INF.FactorsThrough Cross.culturalSurface Cross.standingCode → ⊥
_governed-standing-gap-paid =
  Cross.sameCulturalSurfaceCannotRecoverStanding

_contestability-gap-paid :
  INF.FactorsThrough Cross.culturalSurface Cross.contestabilityCode → ⊥
_contestability-gap-paid =
  Cross.sameCulturalSurfaceCannotRecoverContestability

_material-cone-gap-paid :
  INF.FactorsThrough Cross.culturalSurface Cross.materialConeCode → ⊥
_material-cone-gap-paid =
  Cross.sameCulturalSurfaceCannotRecoverMaterialCone

_rooted-trace-paid :
  Rooted.RootedTraceClaim Cross.powersChapter5Root Cross.powersChapter5Leaf
_rooted-trace-paid = Cross.powersChapter5RootedTraceClaim

_source-theorem-firewall-paid :
  Synthesis.powersSourceClaim ≡ Synthesis.dashiTheorem → ⊥
_source-theorem-firewall-paid =
  Synthesis.sourceClaimDoesNotBecomeDASHITheorem
