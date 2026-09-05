module DASHI.Culture.ScientificRosterWorkCoverageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- COVERAGE LEDGER, NOT A COMMON-THEOREM CLAIM
--
-- This ledger exists to prevent roster members from being forgotten while also
-- preventing administrative/security roles from being manufactured into
-- scientific work.  Each entry points to the actual owner or to the reason no
-- science owner is admissible yet.
------------------------------------------------------------------------

data WorkCoverageStatus : Set where
  scientificOwnerImplemented
  engineeringOwnerImplemented
  programmeRoleImplemented
  mechanismDiscriminationOwnerImplemented
  nonScientificRoleNoScienceOwner
  publicationIdentityWeldPending
  additionalWorkSearchOpen
  : WorkCoverageStatus

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
  "additional publication-specific equations only when source-acquired"

leblancCoverage : WorkCoverageEntry
leblancCoverage = work-coverage-entry
  "Joshua LeBlanc"
  engineeringOwnerImplemented
  "Fission Surface Power instrumentation-and-controls technology maturation"
  "DASHI.Physics.Nuclear.LeBlancFissionSurfacePowerICBidiExact"
  "subsystem-specific control/sensor models when source-owned"

maiwaldCoverage : WorkCoverageEntry
maiwaldCoverage = work-coverage-entry
  "Frank W. Maiwald"
  scientificOwnerImplemented
  "action spectroscopy plus planetary quadrupole-ion-trap mass spectrometry"
  "DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopyBidiExact + MaiwaldQuadrupoleIonTrapMassSpectrometryBidiExact"
  "instrument-response equations and additional mass-spectrometry publications"

rezaCoverage : WorkCoverageEntry
rezaCoverage = work-coverage-entry
  "Monica Jacinto / Monica Reza"
  engineeringOwnerImplemented
  "burn-resistant high-tensile nickel-alloy design"
  "DASHI.Physics.Materials.RezaBurnResistantAlloyBidiExact"
  "processing/microstructure/property data from patent examples or later papers"

grillmairCoverage : WorkCoverageEntry
grillmairCoverage = work-coverage-entry
  "Carl J. Grillmair"
  scientificOwnerImplemented
  "South Galactic Cap stellar-stream detection and Galactic-potential inference"
  "DASHI.Physics.Astrophysics.GrillmairStellarStreamBidiExact"
  "stream-specific orbit/likelihood machinery when source-acquired"

hicksCoverage : WorkCoverageEntry
hicksCoverage = work-coverage-entry
  "Michael D. Hicks"
  scientificOwnerImplemented
  "comet spectrophotometry, archived NEAT photometry, small-body physical inference"
  "DASHI.Physics.Planetary.HicksSmallBodyPhotometryBidiExact + HicksCometAsteroidSpecificWorksBidiExact"
  "additional mission/publication-specific physical models"

mccaslandCoverage : WorkCoverageEntry
mccaslandCoverage = work-coverage-entry
  "William Neil McCasland"
  scientificOwnerImplemented
  "fault-tolerant sensor/actuator selection for flexible structures; later programme/space-system roles"
  "DASHI.Control.McCaslandFaultTolerantFlexibleStructureControlBidiExact + DASHI.Culture.McCaslandTechnicalProgrammeBidiExact"
  "thesis algorithm details / finite-element examples if full thesis equations are acquired"

anthonyChavezCoverage : WorkCoverageEntry
anthonyChavezCoverage = work-coverage-entry
  "Anthony Chavez"
  engineeringOwnerImplemented
  "DARHT engineering and Scorpius accelerator design work"
  "DASHI.Physics.Accelerator.AnthonyChavezScorpiusBidiExact"
  "publication authorship remains separate where identity is not welded"

markAnthonyChavezCoverage : WorkCoverageEntry
markAnthonyChavezCoverage = work-coverage-entry
  "Mark Anthony Chavez"
  publicationIdentityWeldPending
  "compact permanent-magnet spectrometer calibration publication"
  "DASHI.Physics.Accelerator.AnthonyChavezPermanentMagnetSpectrometerCalibrationBidiExact"
  "same-person receipt required before merging with Anthony Chavez roster identity"

jasonThomasCoverage : WorkCoverageEntry
jasonThomasCoverage = work-coverage-entry
  "Jason R. Thomas"
  scientificOwnerImplemented
  "STING-IRF3/NFkB chemical-biology screen and VPS34/NCOA4 ferritinophagy"
  "DASHI.Biology.JasonThomasSignallingBidiExact"
  "publication-specific assay/kinetic detail when source-acquired"

amyEskridgeCoverage : WorkCoverageEntry
amyEskridgeCoverage = work-coverage-entry
  "Amy Eskridge"
  mechanismDiscriminationOwnerImplemented
  "engineered inertial/gravitational mechanism families discussed in her research programme"
  "DASHI.Culture.AmyEskridgeGravityMechanismCrossPollinationExact"
  "attach authored experimental/paper object only when a primary work receipt is located"

melissaCasiasCoverage : WorkCoverageEntry
melissaCasiasCoverage = work-coverage-entry
  "Melissa Casias"
  nonScientificRoleNoScienceOwner
  "administrative LANL role"
  "DASHI.Culture.MissingDeceasedScientificWorkCrossPollinationExact"
  "do not create science owner without scientific-work receipt"

stevenGarciaCoverage : WorkCoverageEntry
stevenGarciaCoverage = work-coverage-entry
  "Steven Garcia"
  nonScientificRoleNoScienceOwner
  "property-custodian role at Kansas City National Security Campus"
  "DASHI.Culture.MissingDeceasedScientificWorkCrossPollinationExact"
  "do not create science owner without scientific-work receipt"

matthewSullivanCoverage : WorkCoverageEntry
matthewSullivanCoverage = work-coverage-entry
  "Matthew Sullivan"
  nonScientificRoleNoScienceOwner
  "reported former Air Force intelligence role"
  "DASHI.Culture.MissingDeceasedScientificWorkCrossPollinationExact"
  "do not create science owner without scientific-work receipt"

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

canonicalCoverageBoundary : CoverageBoundary
canonicalCoverageBoundary = coverage-boundary false refl true refl false refl true refl
