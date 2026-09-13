module DASHI.Law.SensibLawWoogarooPreservationLegalCutsetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooBartyOutreachExact as Woogaroo
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Law.SensibLawIndigenousCustodianshipDutyCrossPollinationExact as Custodianship

------------------------------------------------------------------------
-- WOOGAROO FOREST PRESERVATION LEGAL CUTSET
--
-- Purpose:
--   identify source-paid legal mechanisms capable of restraining, refusing,
--   suspending, or structurally preventing habitat loss at Woogaroo.
--
-- Provenance discipline:
--   external source proposition
--     != DASHI legal reconstruction
--     != cross-source application/inference
--     != adjudicated finding
--     != realised protective outcome.
--
-- A project delay is represented separately from legal protection.  Delay may
-- alter procedural state or create an intervention window; it does not by
-- itself prove refusal, prohibition, habitat status, or permanent protection.
------------------------------------------------------------------------

data SourceRole : Set where
  primaryLegislation : SourceRole
  primaryGovernmentRecord : SourceRole
  proponentEcologyMaterial : SourceRole
  campaignClassification : SourceRole
  dashiReconstruction : SourceRole
  dashiCrossSourceInference : SourceRole
  externalAdjudication : SourceRole

record LegalSourceAttribution : Set where
  constructor legal-source-attribution
  field
    sourceRole : SourceRole
    authorInstitution : String
    titleOrInstrument : String
    exactLocator : String
    boundedProposition : String
    sourcePaid : Bool
    sourcePaidIsTrue : sourcePaid ≡ true
    propositionIsAdjudicatedFinding : Bool

open LegalSourceAttribution public

------------------------------------------------------------------------
-- Procedural state is not protection.
------------------------------------------------------------------------

data ProjectProceduralState : Set where
  referred : ProjectProceduralState
  underAssessment : ProjectProceduralState
  delayed : ProjectProceduralState
  approved : ProjectProceduralState
  refused : ProjectProceduralState
  withdrawn : ProjectProceduralState
  unknown : ProjectProceduralState

data ProtectionState : Set where
  noProtectionShown : ProtectionState
  temporaryRestraint : ProtectionState
  approvalLegallyConstrained : ProtectionState
  permanentProtection : ProtectionState

record ProceduralProtectionBoundary : Set where
  constructor procedural-protection-boundary
  field
    delayEqualsRefusal : Bool
    delayEqualsRefusalIsFalse : delayEqualsRefusal ≡ false
    delayEqualsPermanentProtection : Bool
    delayEqualsPermanentProtectionIsFalse : delayEqualsPermanentProtection ≡ false
    delayMayCreateInterventionWindow : Bool
    delayMayCreateInterventionWindowIsTrue : delayMayCreateInterventionWindow ≡ true

canonicalProceduralProtectionBoundary : ProceduralProtectionBoundary
canonicalProceduralProtectionBoundary =
  procedural-protection-boundary false refl false refl true refl

------------------------------------------------------------------------
-- Ecological coordinates.  These are deliberately finer than a slogan such as
-- "threatened species present" because each legal mechanism has a different
-- statutory consumer.
------------------------------------------------------------------------

data EcologicalCoordinate : Set where
  listedThreatenedSpecies : EcologicalCoordinate
  listedThreatenedEcologicalCommunity : EcologicalCoordinate
  endangeredOrVulnerableWildlifeHabitat : EcologicalCoordinate
  criticalHabitatEvidence : EcologicalCoordinate
  breedingForagingRoostingHabitat : EcologicalCoordinate
  habitatConnectivity : EcologicalCoordinate
  cumulativeFragmentation : EcologicalCoordinate
  threatenedFlora : EcologicalCoordinate
  imminentThreateningProcess : EcologicalCoordinate

data LegalMechanism : Set where
  qldNCASection13CriticalHabitat : LegalMechanism
  qldNCASection49CompulsoryNatureRefuge : LegalMechanism
  qldNCASection102InterimConservationOrder : LegalMechanism
  qldNCAPart7APlanningConstraint : LegalMechanism
  commonwealthEPBCSection18ThreatenedSpecies : LegalMechanism
  commonwealthEPBCApprovalRefusal : LegalMechanism
  commonwealthEPBCSection475Injunction : LegalMechanism
  qldNCASection173DEnforcementOrder : LegalMechanism
  vegetationManagementConstraint : LegalMechanism
  planningSchemeConstraint : LegalMechanism
  protectiveAcquisitionOrTenure : LegalMechanism

data MechanismEffect : Set where
  evidenceClassification : MechanismEffect
  ministerialDiscretion : MechanismEffect
  temporaryProhibitionOrControl : MechanismEffect
  approvalConstraint : MechanismEffect
  refusalRoute : MechanismEffect
  judicialRestraint : MechanismEffect
  permanentTenureProtection : MechanismEffect

record PreservationGate : Set where
  constructor preservation-gate
  field
    mechanism : LegalMechanism
    targetEffect : MechanismEffect
    statutoryOrLegalTest : String
    evidenceNeeded : String
    authoritySource : LegalSourceAttribution
    currentlyPaid : Bool
    currentlyPaidReason : String
    automaticProtectionIfPaid : Bool
    residual : String

open PreservationGate public

------------------------------------------------------------------------
-- Source-attributed authority carriers.
--
-- These are bounded propositions, not findings about Woogaroo itself.
------------------------------------------------------------------------

ncaCriticalHabitatDefinition : LegalSourceAttribution
ncaCriticalHabitatDefinition = legal-source-attribution
  primaryLegislation
  "Queensland"
  "Nature Conservation Act 1992 (Qld)"
  "s 13"
  "Critical habitat is habitat essential for conservation of a viable population of protected wildlife or a community of native wildlife; occupation at the relevant time is not necessarily required."
  true refl false

ncaCompulsoryNatureRefugeAuthority : LegalSourceAttribution
ncaCompulsoryNatureRefugeAuthority = legal-source-attribution
  primaryLegislation
  "Queensland"
  "Nature Conservation Act 1992 (Qld)"
  "s 49"
  "Where agreement cannot be reached, the statutory scheme provides a compulsory nature-refuge declaration route for land considered to include an area of major interest or critical habitat and suitable for nature-refuge protection."
  true refl false

ncaInterimConservationOrderAuthority : LegalSourceAttribution
ncaInterimConservationOrderAuthority = legal-source-attribution
  primaryLegislation
  "Queensland"
  "Nature Conservation Act 1992 (Qld)"
  "ss 102-107"
  "The statutory scheme provides interim conservation orders capable of prohibiting or controlling threatening processes and associated authority-suspension consequences where the statutory conditions are met."
  true refl false

ncaPlanningConstraintAuthority : LegalSourceAttribution
ncaPlanningConstraintAuthority = legal-source-attribution
  primaryLegislation
  "Queensland"
  "Nature Conservation Act 1992 (Qld)"
  "Part 7A"
  "Where land is formally identified under the statutory critical-habitat/area-of-major-interest mechanism, inconsistent local-government approvals may be constrained by the Act."
  true refl false

epbcThreatenedSpeciesAuthority : LegalSourceAttribution
epbcThreatenedSpeciesAuthority = legal-source-attribution
  primaryLegislation
  "Commonwealth of Australia"
  "Environment Protection and Biodiversity Conservation Act 1999 (Cth)"
  "ss 18, 18A; Part 9"
  "Actions likely to have a significant impact on listed threatened species or ecological communities engage the EPBC controlled-action and approval regime."
  true refl false

epbcInjunctionAuthority : LegalSourceAttribution
epbcInjunctionAuthority = legal-source-attribution
  primaryLegislation
  "Commonwealth of Australia"
  "Environment Protection and Biodiversity Conservation Act 1999 (Cth)"
  "s 475"
  "The Federal Court has statutory injunction jurisdiction in relation to conduct constituting or threatening contravention of the EPBC Act, subject to the Act's standing and procedural requirements."
  true refl false

qldEnforcementAuthority : LegalSourceAttribution
qldEnforcementAuthority = legal-source-attribution
  primaryLegislation
  "Queensland"
  "Nature Conservation Act 1992 (Qld)"
  "s 173D"
  "The Act provides an enforcement-order route to restrain or remedy nominated offences, subject to the statutory conditions."
  true refl false

------------------------------------------------------------------------
-- Woogaroo source coordinates already paid in the repository.
------------------------------------------------------------------------

woogarooCatchmentCarrier : LegalSourceAttribution
woogarooCatchmentCarrier = legal-source-attribution
  primaryGovernmentRecord
  "Ipswich City Council"
  "Woogaroo Creek / Opossum Creek catchment and Platypus Recovery Plan material"
  "Woogaroo sub-catchment; recovery areas WG2/WG3/OP1"
  "Opossum Creek is within the Woogaroo Creek sub-catchment; Council material records significant vegetation/wildlife linkages and high-quality habitat in the Opossum Creek system."
  true refl false

scenicFederalAssessmentCarrier : LegalSourceAttribution
scenicFederalAssessmentCarrier = legal-source-attribution
  primaryGovernmentRecord
  "Commonwealth EPBC public portal"
  "Scenic Precinct, Springfield — EPBC 2020/8651"
  "project record / preliminary documentation"
  "The Scenic Precinct proposal is an EPBC-referred project under assessment with threatened-species / ecological-community controlling provisions identified in the federal record."
  true refl false

peninsulaFederalAssessmentCarrier : LegalSourceAttribution
peninsulaFederalAssessmentCarrier = legal-source-attribution
  primaryGovernmentRecord
  "Commonwealth EPBC public portal"
  "Peninsula Precinct, Springfield — EPBC 2020/8629"
  "project record"
  "The Peninsula Precinct proposal is an EPBC-referred project under assessment."
  true refl false

------------------------------------------------------------------------
-- Critical WrongType boundary: a proponent's use of the words "critical
-- habitat" in federal ecology material does not definitionally prove the
-- Queensland NCA s 13 legal classification.  The ecological facts can be
-- evidence for both consumers, but each legal test must be paid separately.
------------------------------------------------------------------------

data EPBCCriticalHabitatEqualsNCAS13CriticalHabitat : Set where

epbcCriticalHabitatDoesNotAutoPayNCAS13 :
  EPBCCriticalHabitatEqualsNCAS13CriticalHabitat → ⊥
epbcCriticalHabitatDoesNotAutoPayNCAS13 ()

------------------------------------------------------------------------
-- Current preservation cutset.
------------------------------------------------------------------------

criticalHabitatClassificationGate : PreservationGate
criticalHabitatClassificationGate = preservation-gate
  qldNCASection13CriticalHabitat
  evidenceClassification
  "Show that the relevant Woogaroo habitat satisfies the Queensland s 13 critical-habitat test for protected wildlife or a native-wildlife community."
  "Species/community identity + conservation status + mapped habitat function + evidence that the habitat is essential to viable-population/community conservation."
  ncaCriticalHabitatDefinition
  false
  "Threatened-species and habitat evidence exists, but this owner does not yet carry a source-paid same-footprint s 13 application receipt."
  false
  "Obtain authoritative ecology mapping/opinion applying the Queensland statutory test to the exact threatened parcels."

compulsoryNatureRefugeGate : PreservationGate
compulsoryNatureRefugeGate = preservation-gate
  qldNCASection49CompulsoryNatureRefuge
  permanentTenureProtection
  "Establish statutory suitability for the compulsory nature-refuge route, including critical habitat or area-of-major-interest basis and the required ministerial/Governor in Council process."
  "Paid s 13/area-of-major-interest evidence + exact land parcels + ownership/tenure + evidence supporting nature-refuge suitability + procedural initiation."
  ncaCompulsoryNatureRefugeAuthority
  false
  "The legal mechanism is source-paid; the Woogaroo-specific statutory application and executive decision are not."
  false
  "Prepare a parcel-specific ministerial request supported by the strongest critical-habitat evidence."

interimConservationOrderGate : PreservationGate
interimConservationOrderGate = preservation-gate
  qldNCASection102InterimConservationOrder
  temporaryProhibitionOrControl
  "Show the statutory wildlife/habitat condition plus a threatening process likely to cause significant detrimental effect."
  "Current threatened wildlife or critical-habitat evidence + exact imminent clearing/development process + timing and impact evidence."
  ncaInterimConservationOrderAuthority
  false
  "Delay may increase the available intervention window, but delay itself does not establish the s 102 trigger."
  false
  "Bind the delayed project state to an exact threatened process and current ecological evidence, then request ministerial action before works commence."

part7APlanningConstraintGate : PreservationGate
part7APlanningConstraintGate = preservation-gate
  qldNCAPart7APlanningConstraint
  approvalConstraint
  "Obtain the formal statutory identification needed for the Part 7A inconsistency constraint."
  "Exact statutory instrument/regulation identifying the relevant land + parcel correspondence to the proposed approval footprint."
  ncaPlanningConstraintAuthority
  false
  "No Woogaroo-specific formal Part 7A identification is carried here yet."
  true
  "Determine whether any existing identification applies; if not, identify the pathway and evidentiary package required to seek it."

epbcSignificantImpactGate : PreservationGate
epbcSignificantImpactGate = preservation-gate
  commonwealthEPBCSection18ThreatenedSpecies
  approvalConstraint
  "Show likely significant impact on listed threatened species or ecological communities for the exact referred action."
  "Referral/proponent ecology + species/community listing + habitat loss/fragmentation evidence + controlling-provision correspondence."
  epbcThreatenedSpeciesAuthority
  true
  "The federal project records already identify threatened-species/ecological-community controlling provisions; final approval/refusal remains a separate decision."
  false
  "Compile each project's own ecological concessions into a species/community x impact x controlling-provision matrix and test whether avoidance is legally/ factually available."

epbcRefusalGate : PreservationGate
epbcRefusalGate = preservation-gate
  commonwealthEPBCApprovalRefusal
  refusalRoute
  "Use the assessment record and applicable Part 9 constraints to seek refusal or conditions that prevent the damaging action."
  "Complete assessment record + conservation advice/recovery-plan constraints where applicable + unavoidable residual-impact evidence + alternatives/avoidance analysis."
  epbcThreatenedSpeciesAuthority
  false
  "Referral/assessment status does not equal refusal; the delayed/under-assessment state leaves the decision residual open."
  false
  "Attack the exact approval criteria with source-paid ecological propositions and distinguish avoidance from offset-only mitigation."

epbcInjunctionGate : PreservationGate
epbcInjunctionGate = preservation-gate
  commonwealthEPBCSection475Injunction
  judicialRestraint
  "Identify conduct constituting or threatening an EPBC contravention and satisfy the statutory standing/procedural route."
  "Exact proposed conduct + approval status/conditions + threatened contravention + applicant standing evidence."
  epbcInjunctionAuthority
  false
  "A lawful but environmentally harmful approved action is not automatically an EPBC contravention."
  false
  "Keep as an enforcement backstop if works threaten to outrun or breach the federal approval regime."

qldEnforcementGate : PreservationGate
qldEnforcementGate = preservation-gate
  qldNCASection173DEnforcementOrder
  judicialRestraint
  "Identify a nominated Nature Conservation Act offence and the statutory basis for an enforcement order."
  "Exact conduct + offence provision + wildlife/habitat/protected-area status + evidentiary chronology."
  qldEnforcementAuthority
  false
  "No offence is inferred merely from development pressure or threatened-species presence."
  false
  "Map any proposed clearing/take/disturbance conduct to exact offence and permit provisions before relying on this route."

------------------------------------------------------------------------
-- Minimal preservation cutset: the shortest plausible chain to a result that
-- physically keeps habitat in place uses independent temporary and permanent
-- lanes plus the already-live federal approval lane.
------------------------------------------------------------------------

data PreservationCutsetCoordinate : Set where
  exactParcelIdentity : PreservationCutsetCoordinate
  exactThreatenedSpeciesCommunity : PreservationCutsetCoordinate
  queenslandCriticalHabitatApplication : PreservationCutsetCoordinate
  imminentThreateningProcessEvidence : PreservationCutsetCoordinate
  federalSignificantImpactRecord : PreservationCutsetCoordinate
  permanentProtectionDecision : PreservationCutsetCoordinate

data PreservationOutcome : Set where
  habitatMayStillBeLost : PreservationOutcome
  worksTemporarilyRestrained : PreservationOutcome
  damagingApprovalRefused : PreservationOutcome
  habitatPermanentlyProtected : PreservationOutcome

record WoogarooPreservationCutset : Set where
  constructor woogaroo-preservation-cutset
  field
    criticalHabitatGate : PreservationGate
    interimOrderGate : PreservationGate
    natureRefugeGate : PreservationGate
    federalImpactGate : PreservationGate
    federalRefusalGate : PreservationGate
    federalInjunctionGate : PreservationGate

open WoogarooPreservationCutset public

currentWoogarooPreservationCutset : WoogarooPreservationCutset
currentWoogarooPreservationCutset = woogaroo-preservation-cutset
  criticalHabitatClassificationGate
  interimConservationOrderGate
  compulsoryNatureRefugeGate
  epbcSignificantImpactGate
  epbcRefusalGate
  epbcInjunctionGate

------------------------------------------------------------------------
-- Intersectional / custodianship firewall.
-- Ecological protection is necessary but does not exhaust Country authority,
-- custodianship, permission, community mandate, or remedial justice.
------------------------------------------------------------------------

data EcologicalProtectionPaysCustodialAuthority : Set where
data StatutoryNatureRefugeEqualsCountryAuthority : Set where
data DevelopmentRefusalEqualsCompleteRelationalJustice : Set where

ecologicalProtectionDoesNotPayCustodialAuthority :
  EcologicalProtectionPaysCustodialAuthority → ⊥
ecologicalProtectionDoesNotPayCustodialAuthority ()

natureRefugeDoesNotConstituteCountryAuthority :
  StatutoryNatureRefugeEqualsCountryAuthority → ⊥
natureRefugeDoesNotConstituteCountryAuthority ()

refusalDoesNotCompleteRelationalJustice :
  DevelopmentRefusalEqualsCompleteRelationalJustice → ⊥
refusalDoesNotCompleteRelationalJustice ()

------------------------------------------------------------------------
-- High-alpha acquisition ordering.
------------------------------------------------------------------------

data AcquisitionPriority : Set where
  priority1ExactProjectAndParcelMap : AcquisitionPriority
  priority2SpeciesHabitatEvidenceMatrix : AcquisitionPriority
  priority3NCAS13ApplicationEvidence : AcquisitionPriority
  priority4CurrentWorksAndDelayChronology : AcquisitionPriority
  priority5MinisterialProtectionRequest : AcquisitionPriority
  priority6EPBCApprovalAttack : AcquisitionPriority
  priority7EnforcementBackstop : AcquisitionPriority

record NextBestAcquisition : Set where
  constructor next-best-acquisition
  field
    priority : AcquisitionPriority
    description : String
    paysGate : LegalMechanism

currentNextBestAcquisition : NextBestAcquisition
currentNextBestAcquisition = next-best-acquisition
  priority1ExactProjectAndParcelMap
  "Build an exact cadastral/project-footprint map linking each delayed or live Woogaroo proposal to the habitat and threatened-species evidence already carried in its own assessment material."
  qldNCASection13CriticalHabitat
