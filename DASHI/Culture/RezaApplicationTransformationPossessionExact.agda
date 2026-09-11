module DASHI.Culture.RezaApplicationTransformationPossessionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
import DASHI.Core.ApplicationTransformationCapabilityBidiExact as T

data PossessionStatus : Set where sourceBacked partial notLocated : PossessionStatus
record ApplicationRoleReceipt : Set where
  constructor application-role-receipt
  field roleOrPerson : String; transformationCoordinates : List T.TransformationCoordinate; status : PossessionStatus; sourceReference : String; boundedReading : String
open ApplicationRoleReceipt public

jacintoAlloyDesignRole : ApplicationRoleReceipt
jacintoAlloyDesignRole = application-role-receipt "Monica A. Jacinto"
  (T.constitutiveConfiguration ∷ T.sourceOrAlgorithmImplementation ∷ T.integrationWorkflow ∷ []) sourceBacked
  "US20030053926A1; US20040208777A1"
  "Named co-inventor; the public patent discloses composition ranges, element-role reasoning, example performance, and VIM/VAR plus mechanical-working process description."

rezaJPLMaterialsProcessingRoleLead : ApplicationRoleReceipt
rezaJPLMaterialsProcessingRoleLead = application-role-receipt "Monica Jacinto Reza / reported Director of the Materials Processing Group at NASA JPL"
  (T.integrationWorkflow ∷ T.qualificationEvidence ∷ T.tacitExecutionKnowledge ∷ []) partial
  "Contemporaneous public professional-network post by JPL colleague Allan Petre after the 2025-06-22 disappearance; 2026 House Oversight letter repeats public reporting"
  "A JPL colleague publicly described Reza as Director of the Materials Processing Group at NASA JPL, and a later House letter repeated that role. This materially strengthens event-time role attribution but remains colleague testimony plus congressional repetition, not a primary JPL personnel/organization record."

rezaValidatedProcessWindowOwnership : ApplicationRoleReceipt
rezaValidatedProcessWindowOwnership = application-role-receipt "Monica Jacinto/Reza"
  (T.operatingWindow ∷ T.failureHistory ∷ T.qualificationEvidence ∷ T.tacitExecutionKnowledge ∷ []) notLocated
  "bounded public patent/search record"
  "The patent and event-time role reporting do not close exact heat-treatment schedules, gamma-prime/grain-state tolerances, failed-batch history, engine/flight qualification evidence, or person-specific tacit manufacturing ownership."

record EventTimeRoleAttributionState : Set where
  constructor event-time-role-attribution-state
  field
    colleagueRoleTestimonyLocated : Bool
    congressionalRoleRepetitionLocated : Bool
    primaryJPLPersonnelRecordLocated : Bool
    primaryJPLOrgChartOrDirectoryLocated : Bool
    eventTimeRoleStrongCandidate : Bool
    eventTimeRoleExactPrimaryReceiptPaid : Bool
    reportedRoleEqualsMondaloyProcessOwnership : Bool

open EventTimeRoleAttributionState public

canonicalEventTimeRoleAttributionState : EventTimeRoleAttributionState
canonicalEventTimeRoleAttributionState = event-time-role-attribution-state
  true true false false true false false

------------------------------------------------------------------------
-- Cal State LA Dean's Advisory Board historical-page snowball boundary.
--
-- Multiple later secondary pages repeat that the 2024-2025 Cal State LA board
-- showed "Monica Reza — JPL NASA".  The currently recoverable PRIMARY Cal
-- State LA board page is explicitly the 2025-2026 board and does not expose
-- the prior year's Monica row.  Therefore the historical row remains a useful
-- acquisition lead, but source-of-source repetition is not independent proof.
------------------------------------------------------------------------

record HistoricalBoardRoleLead : Set where
  constructor historical-board-role-lead
  field
    institution : String
    currentPrimaryPage : String
    currentPageBoardYear : String
    allegedHistoricalRow : String
    historicalRowRepeatedBySecondarySources : Bool
    exactHistoricalPrimaryPageRecovered : Bool
    historicalPageArchiveOrSnapshotRecovered : Bool
    historicalRowPaysJPLEmployment : Bool
    currentPageAbsenceDisprovesHistoricalRow : Bool
    repeatedSecondaryTextCountsAsIndependentPrimaryReceipts : Bool

open HistoricalBoardRoleLead public

rezaCalStateBoardHistoricalLead : HistoricalBoardRoleLead
rezaCalStateBoardHistoricalLead = historical-board-role-lead
  "Cal State LA College of Engineering, Computer Science, and Technology"
  "https://www.calstatela.edu/ecst/deans-advisory-board"
  "2025-2026"
  "reported 2024-2025 row: Monica Reza — JPL NASA"
  true false false false false false

record HistoricalBoardBoundary : Set where
  constructor historical-board-boundary
  field
    currentPrimaryPageIsEvidenceForCurrentMembership : Bool
    currentPrimaryPageDeterminesPriorYearContents : Bool
    historicalSecondaryRepetitionMaySeedArchiveSearch : Bool
    historicalSecondaryRepetitionPaysPrimaryJPLRole : Bool
    exactArchivedCalStateRowWouldPayInstitutionalAffiliationCoordinate : Bool
    exactArchivedCalStateRowWouldByItselfPayDirectorTitle : Bool

canonicalHistoricalBoardBoundary : HistoricalBoardBoundary
canonicalHistoricalBoardBoundary = historical-board-boundary
  true false true false true false

record RezaApplicationBoundary : Set where
  constructor reza-application-boundary
  field
    coInventorImpliesSoleApplicationHolder : Bool
    patentRecipeImpliesCompleteManufacturingCapability : Bool
    constitutiveDesignRoleSourceBacked : Bool
    validatedProcessWindowOwnershipClosed : Bool
    colleagueTestimonyEqualsPrimaryJPLPersonnelRecord : Bool
    materialsProcessingDirectorImpliesMondaloyStillInActivePortfolio : Bool
    eventTimeRoleMayGuidePrimaryJPLAcquisition : Bool

open RezaApplicationBoundary public

canonicalRezaApplicationBoundary : RezaApplicationBoundary
canonicalRezaApplicationBoundary = reza-application-boundary
  false false true false false false true

data RezaApplicationReverseTarget : Set where
  acquirePrimaryJPLEventTimeRoleRecord
  acquireArchivedCalState2024To2025BoardRow
  acquireHeatTreatmentDevelopmentRecords
  acquireMicrostructureAcceptanceWindow
  acquireProcessToleranceAndFailureHistory
  acquireEngineQualificationOwnership
  acquireManufacturingHandover
  acquireSuccessorRole
  acquireRequalificationAfterDeparture : RezaApplicationReverseTarget

firstRezaApplicationTarget : RezaApplicationReverseTarget
firstRezaApplicationTarget = acquireArchivedCalState2024To2025BoardRow
