module DASHI.Culture.ScientificRosterWorkCoverageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- COVERAGE LEDGER, NOT A COMMON-THEOREM CLAIM
------------------------------------------------------------------------

data WorkCoverageStatus : Set where
  scientificOwnerImplemented : WorkCoverageStatus
  engineeringOwnerImplemented : WorkCoverageStatus
  programmeRoleImplemented : WorkCoverageStatus
  mechanismDiscriminationOwnerImplemented : WorkCoverageStatus
  nonScientificRoleNoScienceOwner : WorkCoverageStatus
  personIdentityWeldPending : WorkCoverageStatus
  publicationIdentityWeldPending : WorkCoverageStatus
  additionalWorkSearchOpen : WorkCoverageStatus

record WorkCoverageEntry : Set where
  constructor work-coverage-entry
  field
    person : String
    status : WorkCoverageStatus
    ownedObject : String
    ownerModule : String
    nextExactLeaf : String

open WorkCoverageEntry public

loureiroCoverage : WorkCoverageEntry
loureiroCoverage = work-coverage-entry
  "Nuno F. G. Loureiro"
  scientificOwnerImplemented
  "Viriato KREHM/KRMHD, Hermite hierarchy, free energy, plasmoid instability scaling"
  "DASHI.Physics.Plasma.LoureiroViriatoPlasmoidBidiExact"
  "student/advisor and grant reassignment, Viriato/KREHM repository custody and target-specific simulation-state continuation; center leadership and memorial teaching continuity do not pay these leaves"

leblancCoverage : WorkCoverageEntry
leblancCoverage = work-coverage-entry
  "Joshua Kyle LeBlanc"
  engineeringOwnerImplemented
  "Fission Surface Power instrumentation-and-controls technology maturation"
  "DASHI.Physics.Nuclear.LeBlancFissionSurfacePowerICBidiExact"
  "internal freeze/authorship date for the August-2025 role snapshot and first exact post-loss SNP I&C TechMat roster"

maiwaldCoverage : WorkCoverageEntry
maiwaldCoverage = work-coverage-entry
  "Frank W. Maiwald"
  scientificOwnerImplemented
  "action spectroscopy plus planetary quadrupole-ion-trap mass spectrometry"
  "DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopyBidiExact + MaiwaldQuadrupoleIonTrapMassSpectrometryBidiExact"
  "crosswalk 2023 experimental spectra to exact raw/reduced datasets, calculations, figure versions and later publication manifestations"

rezaCoverage : WorkCoverageEntry
rezaCoverage = work-coverage-entry
  "Monica Jacinto / Monica Reza"
  engineeringOwnerImplemented
  "burn-resistant high-tensile nickel-alloy design"
  "DASHI.Physics.Materials.RezaBurnResistantAlloyBidiExact"
  "primary JPL/Caltech event-time Materials Processing role record before person-specific process-window/succession claims"

grillmairCoverage : WorkCoverageEntry
grillmairCoverage = work-coverage-entry
  "Carl J. Grillmair"
  scientificOwnerImplemented
  "South Galactic Cap stellar-stream detection and Galactic-potential inference"
  "DASHI.Physics.Astrophysics.GrillmairStellarStreamBidiExact"
  "same-work/manuscript continuation only as a control; preserve the charged local-crime event fibre separately"

hicksCoverage : WorkCoverageEntry
hicksCoverage = work-coverage-entry
  "Michael David Hicks"
  scientificOwnerImplemented
  "comet spectrophotometry, archived NEAT photometry, small-body physical inference"
  "DASHI.Physics.Planetary.HicksSmallBodyPhotometryBidiExact + HicksCometAsteroidSpecificWorksBidiExact"
  "resolve 2022 JPL departure/unfinished-work transfer before treating 2023 death as a technical-removal event"

mccaslandCoverage : WorkCoverageEntry
mccaslandCoverage = work-coverage-entry
  "William Neil McCasland"
  scientificOwnerImplemented
  "fault-tolerant sensor/actuator selection for flexible structures; later programme/space-system roles"
  "DASHI.Control.McCaslandFaultTolerantFlexibleStructureControlBidiExact + DASHI.Culture.McCaslandTechnicalProgrammeBidiExact"
  "date DBE Consulting role/status and recover a 2025-2026 client/programme carrier; stale ATA prose cannot pay event-time continuity"

------------------------------------------------------------------------
-- Chavez identities are intentionally split.
------------------------------------------------------------------------

missingAnthonyChavezCoverage : WorkCoverageEntry
missingAnthonyChavezCoverage = work-coverage-entry
  "Anthony Chavez, missing Los Alamos resident, DOB 1947-01-07"
  personIdentityWeldPending
  "no scientific/engineering work attached to this missing-person identity yet"
  "DASHI.Culture.ChavezApplicationTransformationPossessionExact"
  "same-person receipt to the LANL Summer-2025 Anthony Chavez profile and/or Mark Anthony Chavez publication identity before any technical work is inherited"

lanlAnthonyChavezCoverage : WorkCoverageEntry
lanlAnthonyChavezCoverage = work-coverage-entry
  "Anthony Chavez, LANL Summer-2025 engineering-profile identity"
  engineeringOwnerImplemented
  "DARHT engineering and completed Scorpius accelerator design work"
  "DASHI.Physics.Accelerator.AnthonyChavezScorpiusBidiExact"
  "independently weld this institutional profile to the missing-person identity before event-time possession or disappearance analysis"

markAnthonyChavezCoverage : WorkCoverageEntry
markAnthonyChavezCoverage = work-coverage-entry
  "Mark Anthony Chavez"
  publicationIdentityWeldPending
  "compact permanent-magnet spectrometer calibration publication"
  "DASHI.Physics.Accelerator.AnthonyChavezPermanentMagnetSpectrometerCalibrationBidiExact"
  "same-person receipt required before merging this publication identity with either other Chavez identity"

jasonThomasCoverage : WorkCoverageEntry
jasonThomasCoverage = work-coverage-entry
  "Jason R. Thomas"
  scientificOwnerImplemented
  "STING-IRF3/NFkB chemical-biology screen and VPS34/NCOA4 ferritinophagy"
  "DASHI.Biology.JasonThomasSignallingBidiExact"
  "final Massachusetts medical-examiner identity/cause/manner if public; keep official preliminary no-foul-play statement distinct from final ME"

amyEskridgeCoverage : WorkCoverageEntry
amyEskridgeCoverage = work-coverage-entry
  "Amy Eskridge"
  mechanismDiscriminationOwnerImplemented
  "engineered inertial/gravitational mechanism families discussed in her research programme"
  "DASHI.Culture.AmyEskridgeGravityMechanismCrossPollinationExact"
  "recover Amy-linked same-object release/transition receipt for the policy-required Marshall EDAA/STI object and exact Institute derivative; do not manufacture M-1531 authorship from transition role or surname"

ningLiCoverage : WorkCoverageEntry
ningLiCoverage = work-coverage-entry
  "Ning Li"
  scientificOwnerImplemented
  "superconducting gravitoelectric/gravitomagnetic theory plus static type-II YBCO gravity constraint experiment"
  "DASHI.Physics.ExoticGravity.LiTorrTheorySourceDiligenceProofSearchExact + DASHI.Physics.ExoticGravity.NingLiYBCOGravityConstraintBidiExact"
  "recover primary UAH/AC Gravity/DoD programme lineage and exact 2001 Other Transaction award/technical-results carrier; retain the 1997 <2 parts in 10^8 g static constraint as negative evidence for that tested configuration"

melissaCasiasCoverage : WorkCoverageEntry
melissaCasiasCoverage = work-coverage-entry
  "Melissa Casias"
  nonScientificRoleNoScienceOwner
  "administrative LANL role"
  "DASHI.Culture.MissingDeceasedScientificWorkCrossPollinationExact"
  "primary New Mexico OMI autopsy/toxicology and law-enforcement carrier; undetermined manner does not pay homicide or suicide"

stevenGarciaCoverage : WorkCoverageEntry
stevenGarciaCoverage = work-coverage-entry
  "Steven Abel Garcia"
  nonScientificRoleNoScienceOwner
  "reported property-custodian role associated with Kansas City National Security Campus"
  "DASHI.Culture.MissingDeceasedScientificWorkCrossPollinationExact"
  "primary employer/contract and property-accountability scope; New Mexico DPS pays missing-person identity/date only, not clearance or nuclear-secret access"

matthewSullivanCoverage : WorkCoverageEntry
matthewSullivanCoverage = work-coverage-entry
  "Matthew James Sullivan"
  nonScientificRoleNoScienceOwner
  "former U.S. Air Force intelligence role"
  "DASHI.Culture.MissingDeceasedScientificWorkCrossPollinationExact"
  "primary cause/manner and any independently documented event-time programme/testimony obligation; anonymous later UAP/crash-retrieval claims remain separate"

nickPopeCoverage : WorkCoverageEntry
nickPopeCoverage = work-coverage-entry
  "Nicholas George Pope"
  nonScientificRoleNoScienceOwner
  "former UK Ministry of Defence civil-service UFO investigation role; later author/media commentator"
  "DASHI.Culture.MissingDeceasedRosterExtensionNingLiNickPopeExact"
  "primary MoD role chronology and any exact event-time disclosure/testimony obligation; UFO investigation does not manufacture scientist status, clearance scope or recovered-craft access"

record CoverageBoundary : Set where
  constructor coverage-boundary
  field
    everyRosterPersonMustHaveScientificEquationOwner : Bool
    everyRosterPersonMustHaveScientificEquationOwnerIsFalse :
      everyRosterPersonMustHaveScientificEquationOwner ≡ false
    realScientificWorkShouldReceiveDomainOwner : Bool
    realScientificWorkShouldReceiveDomainOwnerIsTrue :
      realScientificWorkShouldReceiveDomainOwner ≡ true
    missingScienceReceiptMayBeFilledByRoleSimilarity : Bool
    missingScienceReceiptMayBeFilledByRoleSimilarityIsFalse :
      missingScienceReceiptMayBeFilledByRoleSimilarity ≡ false
    separateWorksMayRemainMathematicallySeparate : Bool
    separateWorksMayRemainMathematicallySeparateIsTrue :
      separateWorksMayRemainMathematicallySeparate ≡ true
    sameNameInstitutionAndTopicMayMergePersonIdentities : Bool
    sameNameInstitutionAndTopicMayMergePersonIdentitiesIsFalse :
      sameNameInstitutionAndTopicMayMergePersonIdentities ≡ false
    transitionRoleMayCreateAuthorship : Bool
    transitionRoleMayCreateAuthorshipIsFalse : transitionRoleMayCreateAuthorship ≡ false

canonicalCoverageBoundary : CoverageBoundary
canonicalCoverageBoundary = coverage-boundary
  false refl true refl false refl true refl false refl false refl
