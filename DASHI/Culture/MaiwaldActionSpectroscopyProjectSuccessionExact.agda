module DASHI.Culture.MaiwaldActionSpectroscopyProjectSuccessionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- JPL SURP SAME-PROJECT SUCCESSION
--
-- JPL's SURP archive lists the same project title in 2023, 2024 and 2025.
-- 2023: Frank W. Maiwald (PI), Robert P. Hodyss, Mathias Weber, Lane Terry.
-- 2024/2025: Deacon J. Nemchick (PI), Robert P. Hodyss, Mathias Weber.
-- This closes project-level leadership succession and overlapping-team
-- continuity. It does not prove transfer of every calibration, qualification,
-- apparatus, failure-history or tacit-execution carrier.
------------------------------------------------------------------------

record ProjectSuccessionReceipt : Set where
  constructor project-succession-receipt
  field
    projectTitle : String
    predecessorPI : String
    successorPI : String
    overlappingTeam : String
    predecessorReference : String
    successorReference : String
    sameProjectTitleOwned : Bool
    sameProjectTitleOwnedIsTrue : sameProjectTitleOwned ≡ true
    successorPIRecorded : Bool
    successorPIRecordedIsTrue : successorPIRecorded ≡ true
    overlappingTeamRecorded : Bool
    overlappingTeamRecordedIsTrue : overlappingTeamRecorded ≡ true

open ProjectSuccessionReceipt public

maiWaldActionSpectroscopySuccession : ProjectSuccessionReceipt
maiWaldActionSpectroscopySuccession = project-succession-receipt
  "Unambiguous Detection of Biosignatures by Action Spectroscopy"
  "Frank W. Maiwald"
  "Deacon J. Nemchick"
  "Robert P. Hodyss and Mathias Weber continue from FY23 into FY24/FY25; Lane Terry appears in FY23 and as graduate participant in FY24 poster"
  "JPL FY23 SURP poster SP23012p and JPL SURP archive"
  "JPL FY24 poster SP23012p and JPL SURP archive; same project continues in FY25"
  true refl
  true refl
  true refl

------------------------------------------------------------------------
-- Manuscript lineage recovered from the FY23 working-title carrier.
------------------------------------------------------------------------

data ManuscriptRelation : Set where
  workingTitleCarrier : ManuscriptRelation
  publishedScopeChild : ManuscriptRelation

record SpectroscopyPublicationCarrier : Set where
  constructor spectroscopy-publication-carrier
  field
    relation : ManuscriptRelation
    title : String
    publicationDate : String
    authors : String
    identifier : String
    sourceReference : String
    includesMaiwald : Bool
    exactBibliographicIdentityPaid : Bool

open SpectroscopyPublicationCarrier public

fy23WorkingTitleCarrier : SpectroscopyPublicationCarrier
fy23WorkingTitleCarrier = spectroscopy-publication-carrier
  workingTitleCarrier
  "Cryogenic Ion Vibrational Spectroscopy of Protonated and Deprotonated Valine and of Deprotonated Aminovaleric Acid"
  "2023; in preparation"
  "Lane M. Terry; Maddie K. Klumb; Deacon J. Nemchick; Robert P. Hodyss; Frank W. Maiwald; J. Mathias Weber"
  "JPL SURP poster SP23012 / CL#23-5018"
  "JPL FY23 SURP poster SP23012p, Publications item B"
  true true

protonatedValine2024Carrier : SpectroscopyPublicationCarrier
protonatedValine2024Carrier = spectroscopy-publication-carrier
  publishedScopeChild
  "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects"
  "received 2024-05-29; revised 2024-08-06; accepted 2024-08-07; online 2024-08-16; issue 2024-08-29"
  "Lane M. Terry; Maddie K. Klumb; Deacon J. Nemchick; Robert Hodyss; Frank Maiwald; J. Mathias Weber"
  "ACS DOI 10.1021/acs.jpca.4c03552; PMID 39150465; ChemRxiv DOI 10.26434/chemrxiv-2024-2tvc6"
  "Journal of Physical Chemistry A publication history; PubMed 39150465; ChemRxiv preprint"
  true true

deprotonatedStates2025Carrier : SpectroscopyPublicationCarrier
deprotonatedStates2025Carrier = spectroscopy-publication-carrier
  publishedScopeChild
  "Probing Isomers and Conformers by Cryogenic Ion Vibrational Spectroscopy: Deprotonated States of Valine and Aminovaleric Acid"
  "received 2025-05-07; revised 2025-06-12; accepted 2025-06-13; online 2025-06-23; issue 2025-07-03"
  "Lane M. Terry; Maddie K. Klumb; Deacon J. Nemchick; Robert P. Hodyss; J. Mathias Weber"
  "ACS DOI 10.1021/acs.jpca.5c03141; ChemRxiv DOI 10.26434/chemrxiv-2025-xf3d2"
  "Journal of Physical Chemistry A publication history; ChemRxiv preprint; JILA publication list"
  false true

------------------------------------------------------------------------
-- Attribution-safe manifestation split.
--
-- A title family can have multiple public manifestations.  Identifier role is
-- therefore kept distinct from scientific lineage: ChemRxiv DOI, ACS DOI and
-- NTRS record identity are not interchangeable identifiers even where the
-- records clearly refer to the same title/author family.
------------------------------------------------------------------------

data PublicationManifestationKind : Set where
  chemRxivPreprint
  nasaAcceptedManuscriptRecord
  acsVersionOfRecord : PublicationManifestationKind

record PublicationManifestationReceipt : Set where
  constructor publication-manifestation-receipt
  field
    kind : PublicationManifestationKind
    objectTitle : String
    manifestationIdentifier : String
    attribution : String
    sourceReference : String
    exactManifestationIdentityPaid : Bool
    titleAuthorLineageCompatible : Bool
    sameBytesAsVersionOfRecordPaid : Bool
    acquisitionDateIsScientificWorkDate : Bool

open PublicationManifestationReceipt public

protonatedChemRxivManifestation : PublicationManifestationReceipt
protonatedChemRxivManifestation = publication-manifestation-receipt
  chemRxivPreprint
  "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects"
  "10.26434/chemrxiv-2024-2tvc6"
  "Terry; Klumb; Nemchick; Hodyss; Maiwald; Weber"
  "ChemRxiv preprint PDF"
  true true false false

protonatedNASAExternalAcceptedManifestation : PublicationManifestationReceipt
protonatedNASAExternalAcceptedManifestation = publication-manifestation-receipt
  nasaAcceptedManuscriptRecord
  "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects"
  "NASA NTRS citation 13797709699197; NTRS DOI field points to 10.26434/chemrxiv-2024-2tvc6"
  "Terry; Klumb; Nemchick; Hodyss; Maiwald; Weber"
  "NASA NTRS external-source record, document type Accepted Manuscript, acquired 2026-06-15"
  true true false false

protonatedACSVersionOfRecordManifestation : PublicationManifestationReceipt
protonatedACSVersionOfRecordManifestation = publication-manifestation-receipt
  acsVersionOfRecord
  "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects"
  "10.1021/acs.jpca.4c03552"
  "Terry; Klumb; Nemchick; Hodyss; Maiwald; Weber"
  "ACS Journal of Physical Chemistry A publication record"
  true true true false

record ManifestationBoundary : Set where
  constructor manifestation-boundary
  field
    chemRxivDOIEqualsACSArticleDOI : Bool
    ntrsDOIFieldMakesNTRSRecordChemRxivObject : Bool
    acceptedManuscriptLabelDeterminesAcceptanceDate : Bool
    ntrsAcquisitionDateDeterminesExperimentDate : Bool
    titleAuthorMatchMaySeedVersionLineageSearch : Bool
    exactVersionOrByteIdentityStillRequiresReceipt : Bool

open ManifestationBoundary public

canonicalManifestationBoundary : ManifestationBoundary
canonicalManifestationBoundary = manifestation-boundary
  false false false false true true

------------------------------------------------------------------------
-- Temporal split around Maiwald's death on 2024-07-04.
------------------------------------------------------------------------

record ManuscriptChronologyBoundary : Set where
  constructor manuscript-chronology-boundary
  field
    maiwaldDeathDate : String
    protonatedReceivedBeforeDeath : Bool
    protonatedRevisedAfterDeath : Bool
    protonatedAcceptedAfterDeath : Bool
    protonatedRetainedMaiwaldAuthorship : Bool
    deprotonatedReceivedAfterDeath : Bool
    deprotonatedOmitsMaiwald : Bool
    preDeathSubmissionImpliesAllExperimentsPreDeath : Bool
    postDeathRevisionImpliesPostDeathScientificContributionByMaiwald : Bool
    laterOmissionImpliesCarrierTransfer : Bool

open ManuscriptChronologyBoundary public

canonicalManuscriptChronologyBoundary : ManuscriptChronologyBoundary
canonicalManuscriptChronologyBoundary = manuscript-chronology-boundary
  "2024-07-04"
  true true true true true true
  false false false

record WorkingTitleScopeFork : Set where
  constructor working-title-scope-fork
  field
    broadWorkingTitleOwned : Bool
    protonatedChildPublished : Bool
    deprotonatedChildPublished : Bool
    maiwaldRetainedOn2024Child : Bool
    maiwaldRetainedOn2025Child : Bool
    laterChildWithoutMaiwaldProvesCalibrationTransfer : Bool
    laterChildWithoutMaiwaldProvesNoMaiwaldContribution : Bool
    scopeForkMayGuideSameCarrierTransferSearch : Bool

open WorkingTitleScopeFork public

canonicalWorkingTitleScopeFork : WorkingTitleScopeFork
canonicalWorkingTitleScopeFork = working-title-scope-fork
  true true true true false false false true

record ProjectVsCarrierBoundary : Set where
  constructor project-vs-carrier-boundary
  field
    projectSuccessionImpliesCalibrationTransferred : Bool
    projectSuccessionImpliesCalibrationTransferredIsFalse :
      projectSuccessionImpliesCalibrationTransferred ≡ false
    successorPIImpliesSameTacitKnowledge : Bool
    successorPIImpliesSameTacitKnowledgeIsFalse :
      successorPIImpliesSameTacitKnowledge ≡ false
    overlappingTeamSupportsContinuitySearch : Bool
    overlappingTeamSupportsContinuitySearchIsTrue :
      overlappingTeamSupportsContinuitySearch ≡ true
    publicationContinuationImpliesSameApplicationCarrierTransferred : Bool
    publicationContinuationImpliesSameApplicationCarrierTransferredIsFalse :
      publicationContinuationImpliesSameApplicationCarrierTransferred ≡ false

canonicalProjectVsCarrierBoundary : ProjectVsCarrierBoundary
canonicalProjectVsCarrierBoundary = project-vs-carrier-boundary
  false refl false refl true refl false refl

data MaiwaldSuccessionReverseTarget : Set where
  acquireApparatusConfigurationContinuity : MaiwaldSuccessionReverseTarget
  acquireCalibrationTransfer : MaiwaldSuccessionReverseTarget
  acquireTagResponseModelContinuity : MaiwaldSuccessionReverseTarget
  acquireFailureHistoryTransfer : MaiwaldSuccessionReverseTarget
  acquireQualificationTransfer : MaiwaldSuccessionReverseTarget
  acquireRepositoryOrNotebookContinuity : MaiwaldSuccessionReverseTarget
  acquireWorkingTitleToPublishedVersionHistory : MaiwaldSuccessionReverseTarget
  acquireExperimentAndDataProductionDates : MaiwaldSuccessionReverseTarget
  acquirePreprintAcceptedManuscriptVersionCrosswalk : MaiwaldSuccessionReverseTarget

manuscriptForkNextTarget : MaiwaldSuccessionReverseTarget
manuscriptForkNextTarget = acquireExperimentAndDataProductionDates
