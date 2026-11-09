module DASHI.Law.SensibLawWoogarooOperativeInstrumentEvidenceCut20261109Exact where

-- EPBC 2019/8575: exact signed 16 Oct 2026 Part 9 primary-instrument
-- footprint, original source-version and condition-48 publication gates.
-- Source: original signed approval (50p), SHA256:
-- f9b591f230458939dbeafc8b6178c148dbbec3e68e5e75f66fd187e2a402b808
--
-- Original sources/authorship: Commonwealth National EPA approval;
-- Saunders Havill Part A PD Issue F 3 July 2026, MWW OAMP Issue D
-- 15 October; BAAM Esk OAMP v6 15 October; One Environment Avonvale
-- OAMP Oes1:v1.2(e) 15 October. Earlier Jan 2026 PD v5 is a distinct
-- HISTORICAL source and its 56-AU OAG arithmetic cannot automatically
-- be claimed as the approved decision calculator. QUT/QCC/RSPCA
-- independent original attribution remains in prior golden owners.
--
-- Numeric area quantities are SOURCE-MAP LABELS, NOT independently
-- recomputed geospatial polygons. All hectares scaled by 10.
-- Two printed decimals/rounding and action-vs-offset habitat scopes
-- remain explicit. No legal breach, filing, actual works or transfer
-- follows from these source arithmetic identities.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)

data Origin : Set where
  signedOctoberApproval januaryPDV5 julyPDIssueF octoberOAMP
    projectPublisherIndependentOfAgency qutOriginal qccOriginal : Origin

data Evidence : Set where
  verifiedOriginal unknownOriginal sourceContradiction : Evidence

record Revision : Set where
  constructor revision
  field
    sourceOrigin : Origin
    identification : String
    exactDocumentObtained : Evidence
open Revision public

signedApproval : Revision
signedApproval = revision signedOctoberApproval
  "Signed Part 9 approval 16 October 2026 EPBC 2019/8575"
  verifiedOriginal

finalJulyPD : Revision
finalJulyPD = revision julyPDIssueF
  "Saunders Havill Preliminary Report (Part A), Issue F, 3 July 2026"
  unknownOriginal

avonvaleFinal : Revision
avonvaleFinal = revision octoberOAMP
  "One Environment Avonvale Oes1:v1.2(e), 15 October 2026"
  unknownOriginal

eskFinal : Revision
eskFinal = revision octoberOAMP
  "BAAM Esk 0102-059 Version 6, 15 October 2026"
  unknownOriginal

mountWalkerFinal : Revision
mountWalkerFinal = revision octoberOAMP
  "Saunders Havill Mount Walker West 9612-E Issue D, 15 October 2026"
  unknownOriginal

proponentPublisherListings : Revision
proponentPublisherListings = revision projectPublisherIndependentOfAgency
  "Stockland Springview web resources list OMP links, 9 Nov 2026"
  verifiedOriginal

-- Actual signed approval: Impact area as defined Attachment A2.
-- 123.0 + 8.2 + 1.2 + 2.5 = 134.9 ha.
definedImpactFootprintTenths :
  1230 + 82 + 12 + 25 ≡ 1349
definedImpactFootprintTenths = refl

-- Signed approval Attachments C2/A2:
-- 162.3 ha koala critical habitat mapped within Action area; 27.3 ha
-- reported retained vegetation. Difference = 135.0 ha, not exactly
-- 134.9 ha; 0.1 ha may be rounding/scope mismatch, not evidence of fraud.
koalaAreaMinusRetentionTenths :
  273 + 1350 ≡ 1623
koalaAreaMinusRetentionTenths = refl

footprintVsFullMinusRetentionTenths :
  1349 + 1 ≡ 1350
footprintVsFullMinusRetentionTenths = refl

-- Operative Annexure A condition 4: 128ha of Koala / Grey-headed
-- Flying-fox / Swift Parrot / Regent Honeyeater habitat each (not
-- simply a historical OAG source input); Collared Delma 0.77ha.
-- C1 Action/Clear/Construct prohibited OUTSIDE Action area;
-- C2 Action/Clear/Construct prohibited WITHIN retention area;
-- C3 Clear/Construct prohibited WITHIN LRSA buffer zone.
data Matter : Set where
  koala flyingFox swiftParrot regentHoneyeater collaredDelma : Matter

habitatClearCapHundredthsHa : Matter → Nat
habitatClearCapHundredthsHa koala = 12800
habitatClearCapHundredthsHa flyingFox = 12800
habitatClearCapHundredthsHa swiftParrot = 12800
habitatClearCapHundredthsHa regentHoneyeater = 12800
habitatClearCapHundredthsHa collaredDelma = 77

fourProtectedSpeciesHabitatCapEqual :
  habitatClearCapHundredthsHa koala ≡
  habitatClearCapHundredthsHa regentHoneyeater
fourProtectedSpeciesHabitatCapEqual = refl

-- Footprint of 134.9ha and species-specific 128ha habitat-clearance
-- ceilings differ by 6.9ha IN PRINTED SOURCE UNITS. It is a spatial
-- accounting gate, not proof that the permitted clearing could exceed
-- its species-specific maximum.
habitatCapVsFootprintHundredths :
  habitatClearCapHundredthsHa koala + 690 ≡ 13490
habitatCapVsFootprintHundredths = refl

-- The historical January 2026 OAG input was 128.0 ha of koala
-- impacted habitat; 6.9 ha difference from signed footprint is real
-- PRINTED-SCOPE arithmetic, not a conclusion of unoffset omission.
historicalOAGImpactVsDefinedFootprint :
  1280 + 69 ≡ 1349
historicalOAGImpactVsDefinedFootprint = refl

-- Phase One 56.4 ha. The remainder of the defined 134.9-ha
-- footprint is 78.5 ha if the printed phase polygons sum to footprint.
-- All phase habitat geometry remains to be spatially checked.
phaseOnePlusOtherFootprint :
  564 + 785 ≡ 1349
phaseOnePlusOtherFootprint = refl

-- Conditions 24/25/48-49/52: distinct prerequisites and time triggers.
data Activity : Set where
  commenceAction clearOrConstructOutsidePhaseOne : Activity

data Site : Set where
  avonvale esk mountWalkerWest : Site

requiredDeclarationBefore : Activity → Site → Bool
requiredDeclarationBefore commenceAction avonvale = true
requiredDeclarationBefore commenceAction esk = true
requiredDeclarationBefore commenceAction mountWalkerWest = false
requiredDeclarationBefore clearOrConstructOutsidePhaseOne avonvale = true
requiredDeclarationBefore clearOrConstructOutsidePhaseOne esk = true
requiredDeclarationBefore clearOrConstructOutsidePhaseOne mountWalkerWest = true

phaseOneDoesNotRequireMWWDeclarationUnderC25 :
  requiredDeclarationBefore commenceAction mountWalkerWest ≡ false
phaseOneDoesNotRequireMWWDeclarationUnderC25 = refl

commencementNeedsBothOtherDeclarations :
  requiredDeclarationBefore commenceAction avonvale ≡ true
commencementNeedsBothOtherDeclarations = refl

outsidePhaseOneNeedsMWWDeclaration :
  requiredDeclarationBefore clearOrConstructOutsidePhaseOne
    mountWalkerWest ≡ true
outsidePhaseOneNeedsMWWDeclaration = refl

record ComplianceSourceState : Set where
  constructor compliance-state
  field
    originalDatedDeclarationReceived : Evidence
    originalActionCommencementReceived : Evidence
    originalOutsidePhaseOneClearingReceived : Evidence
    originalMinisterialPublicationExtensionReceived : Evidence
    exactPublishedApprovedRevisionVerified : Evidence
open ComplianceSourceState public

currentPubliclyAcquiredEvidence : ComplianceSourceState
currentPubliclyAcquiredEvidence =
  compliance-state unknownOriginal unknownOriginal unknownOriginal
    unknownOriginal unknownOriginal

-- Signed 16 Oct approval: C48(a) 15 BUSINESS days after decision for
-- specifically named plans, unless Minister agrees otherwise in writing.
-- 2026 QLD holiday list: no statewide holiday 19 Oct - 6 Nov.
-- 15th weekday after 16 Oct Friday is Friday 6 Nov 2026.
-- This is an ordinary schedule date, NOT an observed publication state.
dateOfApprovalYYYYMMDD : Nat
dateOfApprovalYYYYMMDD = 20261016
ordinary15thBusinessDayYYYYMMDD : Nat
ordinary15thBusinessDayYYYYMMDD = 20261106

-- C49 plans must remain downloadable, current and superseded.
-- C52 commencement notice within five business days after commencement.
-- C24 Avonvale and Esk declarations must precede commencement.
-- C25 MWW declaration precedes *outside Phase One* clearing/construct.
-- See separate original source ledger for all operative text, scope,
-- public-access verification and evidence acquisition.
