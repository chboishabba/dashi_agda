module DASHI.Culture.MissingDeceasedOverlookedDimensionMatrixExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.EventTimeCapabilityAlignmentBidiExact as T
import DASHI.Core.CapabilityFragilityConfoundersBidiExact as F

------------------------------------------------------------------------
-- OVERLOOKED-DIMENSION MATRIX
--
-- Tests dimensions that can mimic, erase or redistribute apparent technical
-- criticality: time, reorganisation, custody, codification, redundancy and
-- event-specific alternative evidence.
------------------------------------------------------------------------

data DimensionState : Set where
  closedPositive : DimensionState
  closedNegative : DimensionState
  partial : DimensionState
  open : DimensionState


record OverlookedCaseRow : Set where
  constructor overlooked-case-row
  field
    person : String
    eventTimeAlignment : DimensionState
    organisationalTransition : DimensionState
    physicalOrDataCustody : DimensionState
    codificationOrRedundancy : DimensionState
    eventSpecificAlternative : DimensionState
    highestAlphaLeaf : String
    boundedReading : String

open OverlookedCaseRow public

eskridgeRow : OverlookedCaseRow
eskridgeRow = overlooked-case-row
  "Amy Eskridge"
  partial partial open partial open
  "recover 2020-2022 Institute/HoloChron apparatus, repository, notebook, company-governance and custody records"
  "Public team/company surfaces exist, but exact experimental object custody and event-time application state remain unresolved."

maiwaldRow : OverlookedCaseRow
maiwaldRow = overlooked-case-row
  "Frank Maiwald"
  closedPositive closedPositive partial closedPositive open
  "test whether project-level succession included same apparatus calibration, qualification and failure-history transfer"
  "JPL project succession and overlapping team are closed; same-carrier transfer remains narrower and open."

mccaslandRow : OverlookedCaseRow
mccaslandRow = overlooked-case-row
  "William Neil McCasland"
  partial closedPositive open partial open
  "recover post-2025 AeroVironment role, portfolio, access and handover records"
  "ATA -> BlueHalo -> AeroVironment creates a source-backed organisational transition surface before disappearance; exact event-time carrier remains open."

loureiroRow : OverlookedCaseRow
loureiroRow = overlooked-case-row
  "Nuno F. G. Loureiro"
  closedPositive partial partial closedPositive closedPositive
  "separate group/application continuity from motive while preserving the authorities' same-suspect event evidence"
  "Scientific work was active and institutionally embedded; MIT reports authorities linked his killer to the Brown University mass shooting, providing strong independent competing event evidence."

hicksRow : OverlookedCaseRow
hicksRow = overlooked-case-row
  "Michael David Hicks"
  closedNegative partial open partial open
  "recover whether any DART/small-body operational role or access continued after his 2022 JPL departure"
  "JPL tenure ended in 2022 and death occurred in 2023; historical mission expertise cannot be promoted to event-time operational possession without a continuity receipt."

chavezRow : OverlookedCaseRow
chavezRow = overlooked-case-row
  "Anthony Chavez"
  partial closedPositive partial closedPositive open
  "recover exact event-time Scorpius/DARHT configuration, calibration, access and same-carrier handover"
  "Public records show distributed multi-lab procedures and design surfaces while exact application-carrier concentration remains unresolved."

leblancRow : OverlookedCaseRow
leblancRow = overlooked-case-row
  "Joshua Kyle LeBlanc"
  closedPositive partial partial closedPositive open
  "recover TechMat qualification/failure-map custody and handover"
  "Named technology-maturation leadership is source-backed inside a visibly distributed executive/working-group structure."

rezaRow : OverlookedCaseRow
rezaRow = overlooked-case-row
  "Monica Jacinto / Reza"
  partial closedPositive open closedPositive open
  "recover validated manufacturing process-window custody, corporate assignment lineage and successor/handover"
  "Patent co-invention and corporate IP assignment show shared/corporate surfaces; exact tacit manufacturing and qualification custody remains open."

record OverlookedDimensionBoundary : Set where
  constructor overlooked-dimension-boundary
  field
    historicalRoleCanSubstituteForEventTimeAlignment : Bool
    historicalRoleCanSubstituteForEventTimeAlignmentIsFalse : historicalRoleCanSubstituteForEventTimeAlignment ≡ false
    projectContinuationProvesSameCarrierTransfer : Bool
    projectContinuationProvesSameCarrierTransferIsFalse : projectContinuationProvesSameCarrierTransfer ≡ false
    reorganisationProvesAdverseEvent : Bool
    reorganisationProvesAdverseEventIsFalse : reorganisationProvesAdverseEvent ≡ false
    eventSpecificAlternativeCanOverrideNarrativeSalience : Bool
    eventSpecificAlternativeCanOverrideNarrativeSalienceIsTrue : eventSpecificAlternativeCanOverrideNarrativeSalience ≡ true

canonicalOverlookedDimensionBoundary : OverlookedDimensionBoundary
canonicalOverlookedDimensionBoundary = overlooked-dimension-boundary false refl false refl false refl true refl
