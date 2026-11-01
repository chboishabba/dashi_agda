module DASHI.Physics.ExoticGravity.NingLiNASACooperativeAgreementNCC8124Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.NingLiYBCOGravityConstraintBidiExact as Static
import DASHI.Physics.ExoticGravity.LiTorrTheorySourceDiligenceProofSearchExact as Theory

------------------------------------------------------------------------
-- NASA/MSFC <-> UAH COOPERATIVE AGREEMENT NCC8-124
--
-- NTRS 20000038203 is a primary NASA contractor/grantee report authored by Ning
-- Li.  It records the 1996-2000 NASA/MSFC-UAH cooperative programme, planned
-- joint all-up measurements using components developed at both organisations,
-- technological difficulties, and failure to complete the challenging final
-- experiments within the agreement term.  This is programme evidence, not an
-- anomalous-gravity result and not the later Army/AC Gravity outcome.
------------------------------------------------------------------------

record NingLiNASAProgrammeReceipt : Set where
  constructor ning-li-nasa-programme-receipt
  field
    author : String
    title : String
    ntrsDocumentId : String
    acquisitionSource : String
    documentType : String
    fundingNumber : String
    publicationDate : String
    subjectCategory : String
    distribution : String
    programmeReading : String
    finalExperimentsCompleted : Bool
    anomalousGravityResultEstablished : Bool
    sourceReference : String

open NingLiNASAProgrammeReceipt public

ncc8124FinalReport : NingLiNASAProgrammeReceipt
ncc8124FinalReport = ning-li-nasa-programme-receipt
  "Ning Li"
  "Cooperative Agreement NCC8-124 Between NASA/MSFC and UAH - Final Report / Activities of UAH"
  "NTRS 20000038203"
  "Marshall Space Flight Center"
  "Contractor or Grantee Report"
  "NCC8-124"
  "2000-01-01"
  "Solid-State Physics"
  "Public"
  "UAH and MSFC divided and jointly developed programme components; the envisioned all-up measurement process was not completed during the agreement because technological difficulties prevented completion of the challenging experiments"
  false false
  "NASA Technical Reports Server citation 20000038203"

------------------------------------------------------------------------
-- Programme chronology relative to already-paid theory and static experiment.
------------------------------------------------------------------------

liTorrTheoryIdentityPresent : Theory.prd1991Candidate ≡ Theory.prd1991Candidate
liTorrTheoryIdentityPresent = refl

static1997ConstraintPresent :
  Static.staticYBCO1997Constraint ≡ Static.staticYBCO1997Constraint
static1997ConstraintPresent = refl

record ProgrammeTransitionResidual : Set where
  constructor programme-transition-residual
  field
    earlierTheory : String
    earlierConstraint : String
    nasaProgramme : String
    reportedLaterArmyProgramme : String
    armyPrimaryCarrierPaid : Bool
    nasaToArmySameApparatusPaid : Bool
    technicalOutcomePaid : Bool
    nextExactAcquisition : String

open ProgrammeTransitionResidual public

nasaToReportedArmyResidual : ProgrammeTransitionResidual
nasaToReportedArmyResidual = programme-transition-residual
  "Li/Torr 1991-1993 superconducting-gravity theory corpus"
  "1997 Physica C static type-II YBCO gravimeter constraint"
  "NASA/MSFC-UAH NCC8-124, NTRS 20000038203"
  "secondary transcriptions identify Army AMCOM Other Transaction DAAH01-01-9-R001 for AC Gravity, 2001-2002"
  false false false
  "recover primary FY2001 DoD annual-report page and underlying Army agreement/statement-of-work/closeout; compare apparatus components, drive regime, personnel and test objectives against NCC8-124 before claiming programme continuity"

nasaProgrammeDoesNotPayArmyOutcome : Bool
nasaProgrammeDoesNotPayArmyOutcome = true

record NingLiNASAProgrammeBoundary : Set where
  constructor ning-li-nasa-programme-boundary
  field
    nasaProgrammeProvesGravityModification : Bool
    incompleteFinalExperimentEqualsSuppression : Bool
    nasaProgrammeAutomaticallySameAsArmyProgramme : Bool
    sharedNingLiIdentityMaySeedTransitionSearch : Bool
    exactApparatusSameObjectReceiptRequired : Bool

canonicalNingLiNASAProgrammeBoundary : NingLiNASAProgrammeBoundary
canonicalNingLiNASAProgrammeBoundary = ning-li-nasa-programme-boundary
  false false false true true
