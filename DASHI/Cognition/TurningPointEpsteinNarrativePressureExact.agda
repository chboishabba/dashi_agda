module DASHI.Cognition.TurningPointEpsteinNarrativePressureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- TURNING POINT USA / EPSTEIN NARRATIVE-PRESSURE SURFACE
--
-- TPUSA is treated here as a political/narrative institution whose events
-- visibly mediated MAGA-base pressure over Epstein-file disclosure.  This does
-- NOT create a TPUSA<->Epstein operational relationship.
------------------------------------------------------------------------

data TPUSEdgeKind : Set where
  studentActionSummitBacklash : TPUSEdgeKind
  bondiDOJCriticism : TPUSEdgeKind
  kirkAdministrationTrustPivot : TPUSEdgeKind
  laterDisclosureDemand : TPUSEdgeKind
  americaFestAttentionCollapse : TPUSEdgeKind
  bannonStagePressure : TPUSEdgeKind
  intelligenceSpeculationSurface : TPUSEdgeKind
  erikaKirkEpsteinRumourUnpaid : TPUSEdgeKind

record TPUSReceipt : Set where
  constructor tpus-receipt
  field
    edgeKind : TPUSEdgeKind
    sourceIdentity : String
    boundedFinding : String
    politicalNarrativeEdgePaid : Bool
    directEpsteinRelationshipPaid : Bool
    factualUnderlyingTheoryPaid : Bool
open TPUSReceipt public

summitBacklashReceipt : TPUSReceipt
summitBacklashReceipt = tpus-receipt
  studentActionSummitBacklash
  "Washington Post, 2025-07-12/13"
  "At TPUSA's 2025 Student Action Summit, attendees booed the Trump administration's handling of Epstein files and movement figures warned of electoral/base costs."
  true false false

bondiCriticismReceipt : TPUSReceipt
bondiCriticismReceipt = tpus-receipt
  bondiDOJCriticism
  "Washington Post, 2025-07-12/13"
  "Megyn Kelly and other speakers criticised Attorney General Pam Bondi/DOJ over non-release and messaging around Epstein records."
  true false false

bannonPressureReceipt : TPUSReceipt
bannonPressureReceipt = tpus-receipt
  bannonStagePressure
  "Washington Post, 2025-07-12/13"
  "Steve Bannon framed the Epstein-file dispute at the TPUSA gathering as a governance/trust issue capable of costing the movement substantial support."
  true false false

kirkPivotReceipt : TPUSReceipt
kirkPivotReceipt = tpus-receipt
  kirkAdministrationTrustPivot
  "Vanity Fair 2025-12-20 retrospect / contemporaneous Kirk statement"
  "Charlie Kirk later said he was done discussing Epstein for the time being and would trust friends in the administration; the statement pays a narrative-position change, not proof of coercion or control."
  true false false

americaFestReceipt : TPUSReceipt
americaFestReceipt = tpus-receipt
  americaFestAttentionCollapse
  "Vanity Fair, 2025-12-20"
  "At AmericaFest during the December 2025 partial file release, major speakers mostly avoided the newly released material and attendee attention was markedly lower than during the July revolt."
  true false false

intelligenceSpeculationReceipt : TPUSReceipt
intelligenceSpeculationReceipt = tpus-receipt
  intelligenceSpeculationSurface
  "public TPUSA-stage/podcast discussion, 2025"
  "TPUSA-associated speakers publicly entertained foreign-intelligence hypotheses around Epstein. This pays the existence of the speculation surface only; it does not establish an intelligence relationship."
  true false false

erikaRumourReceipt : TPUSReceipt
erikaRumourReceipt = tpus-receipt
  erikaKirkEpsteinRumourUnpaid
  "2026 online allegation / TPUSA denial / no current DOJ relationship receipt"
  "Claims linking Erika Kirk to Epstein via modelling-agency genealogy are not promoted absent a primary relationship receipt."
  true false false

record TPUSEpsteinNarrativeBoundary : Set where
  constructor tpus-epstein-narrative-boundary
  field
    tpusaBasePressurePaid : Bool
    leadershipNarrativePivotPaid : Bool
    americaFestAttenuationPaid : Bool
    directTPUSAEpsteinRelationshipPaid : Bool
    foreignIntelligenceTheoryEstablished : Bool
    erikaKirkEpsteinRelationshipPaid : Bool
open TPUSEpsteinNarrativeBoundary public

canonicalTPUSEpsteinNarrativeBoundary : TPUSEpsteinNarrativeBoundary
canonicalTPUSEpsteinNarrativeBoundary =
  tpus-epstein-narrative-boundary true true true false false false

data BasePressureImpliesInstitutionalControl : Set where
data NarrativePivotImpliesExtortion : Set where
data PublicSpeculationImpliesUnderlyingTruth : Set where
data PoliticalEventImpliesEpsteinRelationship : Set where

basePressureDoesNotCreateControl : BasePressureImpliesInstitutionalControl → ⊥
basePressureDoesNotCreateControl ()

narrativePivotDoesNotCreateExtortion : NarrativePivotImpliesExtortion → ⊥
narrativePivotDoesNotCreateExtortion ()

speculationDoesNotCreateTruth : PublicSpeculationImpliesUnderlyingTruth → ⊥
speculationDoesNotCreateTruth ()

politicalEventDoesNotCreateEpsteinRelationship : PoliticalEventImpliesEpsteinRelationship → ⊥
politicalEventDoesNotCreateEpsteinRelationship ()
