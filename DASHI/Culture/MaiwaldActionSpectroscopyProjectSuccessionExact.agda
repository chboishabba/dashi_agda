module DASHI.Culture.MaiwaldActionSpectroscopyProjectSuccessionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- JPL SURP SAME-PROJECT SUCCESSION
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
  true refl true refl true refl

------------------------------------------------------------------------
-- Manuscript lineage recovered from the FY23 working-title carrier.
------------------------------------------------------------------------

data ManuscriptRelation : Set where workingTitleCarrier publishedScopeChild : ManuscriptRelation

record SpectroscopyPublicationCarrier : Set where
  constructor spectroscopy-publication-carrier
  field relation : ManuscriptRelation; title : String; publicationDate : String; authors : String; identifier : String; sourceReference : String; includesMaiwald : Bool; exactBibliographicIdentityPaid : Bool
open SpectroscopyPublicationCarrier public

fy23WorkingTitleCarrier : SpectroscopyPublicationCarrier
fy23WorkingTitleCarrier = spectroscopy-publication-carrier workingTitleCarrier
  "Cryogenic Ion Vibrational Spectroscopy of Protonated and Deprotonated Valine and of Deprotonated Aminovaleric Acid"
  "2023; in preparation"
  "Lane M. Terry; Maddie K. Klumb; Deacon J. Nemchick; Robert P. Hodyss; Frank W. Maiwald; J. Mathias Weber"
  "JPL SURP poster SP23012 / CL#23-5018"
  "JPL FY23 SURP poster SP23012p, Publications item B" true true

protonatedValine2024Carrier : SpectroscopyPublicationCarrier
protonatedValine2024Carrier = spectroscopy-publication-carrier publishedScopeChild
  "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects"
  "received 2024-05-29; revised 2024-08-06; accepted 2024-08-07; online 2024-08-16; issue 2024-08-29"
  "Lane M. Terry; Maddie K. Klumb; Deacon J. Nemchick; Robert Hodyss; Frank Maiwald; J. Mathias Weber"
  "ACS DOI 10.1021/acs.jpca.4c03552; PMID 39150465; ChemRxiv DOI 10.26434/chemrxiv-2024-2tvc6"
  "Journal of Physical Chemistry A publication history; PubMed 39150465; ChemRxiv preprint" true true

deprotonatedStates2025Carrier : SpectroscopyPublicationCarrier
deprotonatedStates2025Carrier = spectroscopy-publication-carrier publishedScopeChild
  "Probing Isomers and Conformers by Cryogenic Ion Vibrational Spectroscopy: Deprotonated States of Valine and Aminovaleric Acid"
  "received 2025-05-07; revised 2025-06-12; accepted 2025-06-13; online 2025-06-23; issue 2025-07-03"
  "Lane M. Terry; Maddie K. Klumb; Deacon J. Nemchick; Robert P. Hodyss; J. Mathias Weber"
  "ACS DOI 10.1021/acs.jpca.5c03141; ChemRxiv DOI 10.26434/chemrxiv-2025-xf3d2"
  "Journal of Physical Chemistry A publication history; ChemRxiv preprint; JILA publication list" false true

------------------------------------------------------------------------
-- Attribution-safe manifestation split.
------------------------------------------------------------------------

data PublicationManifestationKind : Set where chemRxivPreprint nasaAcceptedManuscriptRecord acsVersionOfRecord : PublicationManifestationKind
record PublicationManifestationReceipt : Set where
  constructor publication-manifestation-receipt
  field kind : PublicationManifestationKind; objectTitle : String; manifestationIdentifier : String; attribution : String; sourceReference : String; exactManifestationIdentityPaid : Bool; titleAuthorLineageCompatible : Bool; sameBytesAsVersionOfRecordPaid : Bool; acquisitionDateIsScientificWorkDate : Bool
open PublicationManifestationReceipt public

protonatedChemRxivManifestation = publication-manifestation-receipt chemRxivPreprint "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects" "10.26434/chemrxiv-2024-2tvc6" "Terry; Klumb; Nemchick; Hodyss; Maiwald; Weber" "ChemRxiv preprint PDF" true true false false
protonatedNASAExternalAcceptedManifestation = publication-manifestation-receipt nasaAcceptedManuscriptRecord "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects" "NASA NTRS citation 13797709699197; NTRS DOI field points to 10.26434/chemrxiv-2024-2tvc6" "Terry; Klumb; Nemchick; Hodyss; Maiwald; Weber" "NASA NTRS external-source record, document type Accepted Manuscript, acquired 2026-06-15" true true false false
protonatedACSVersionOfRecordManifestation = publication-manifestation-receipt acsVersionOfRecord "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects" "10.1021/acs.jpca.4c03552" "Terry; Klumb; Nemchick; Hodyss; Maiwald; Weber" "ACS Journal of Physical Chemistry A publication record" true true true false

record ManifestationBoundary : Set where
  constructor manifestation-boundary
  field chemRxivDOIEqualsACSArticleDOI : Bool; ntrsDOIFieldMakesNTRSRecordChemRxivObject : Bool; acceptedManuscriptLabelDeterminesAcceptanceDate : Bool; ntrsAcquisitionDateDeterminesExperimentDate : Bool; titleAuthorMatchMaySeedVersionLineageSearch : Bool; exactVersionOrByteIdentityStillRequiresReceipt : Bool
canonicalManifestationBoundary = manifestation-boundary false false false false true true

------------------------------------------------------------------------
-- Primary 2023 experimental-data existence receipt.
------------------------------------------------------------------------

record ExperimentalDataExistenceReceipt : Set where
  constructor experimental-data-existence-receipt
  field sourceObject : String; sourceDate : String; protonatedExperimentalSpectrumVisible : Bool; deprotonatedValineExperimentalSpectrumVisible : Bool; deprotonatedAminovalericExperimentalSpectrumVisible : Bool; maiwaldPIOrTaskManagerVisible : Bool; broadManuscriptInPreparationVisible : Bool; exactExperimentRunDatesPaid : Bool; exactRawDataBytesPaid : Bool; laterPaperFigureByteIdentityPaid : Bool
open ExperimentalDataExistenceReceipt public

fy23ExperimentalDataExistence = experimental-data-existence-receipt
  "JPL SURP poster SP23012p / CL#23-5018" "2023 poster manifestation"
  true true true true true false false false

record ExperimentalDataBoundary : Set where
  constructor experimental-data-boundary
  field deprotonatedSpectraExistedBy2023 : Bool; protonatedSpectraExistedBy2023 : Bool; therefore2025PublicationCycleWasWhollyPostLossScience : Bool; posterSpectrumImpliesFinal2025DatasetComplete : Bool; posterSpectrumImpliesExactRawDataCustody : Bool; posterMaySeedDatasetVersionCrosswalk : Bool
canonicalExperimentalDataBoundary = experimental-data-boundary true true false false false true

------------------------------------------------------------------------
-- Primary conference manifestation immediately before Maiwald's death.
------------------------------------------------------------------------

record PreLossConferenceDataReceipt : Set where
  constructor pre-loss-conference-data-receipt
  field
    sourceObject : String
    presentationDate : String
    sourceClass : String
    authors : String
    maiwaldAffiliation : String
    deprotonatedValineSpectraPresented : Bool
    deprotonatedAminovalericSpectraPresented : Bool
    maiwaldNamedCoauthor : Bool
    predatesMaiwaldDeath : Bool
    exactInstrumentRunDatesPaid : Bool
    exactRawDataBytesPaid : Bool
    exactIdentityWith2025FinalDatasetPaid : Bool

open PreLossConferenceDataReceipt public

isms2024DeprotonatedSpectraReceipt : PreLossConferenceDataReceipt
isms2024DeprotonatedSpectraReceipt = pre-loss-conference-data-receipt
  "77th International Symposium on Molecular Spectroscopy, official session schedule, P7658 / RL06"
  "2024-06-20 15:15-15:30"
  "primary conference programme/abstract carrier"
  "Lane M. Terry; Deacon J. Nemchick; Robert Hodyss; Frank Maiwald; J. Mathias Weber"
  "Jet Propulsion Laboratory, California Institute of Technology, Pasadena, CA"
  true true true true false false false

record PreLossConferenceBoundary : Set where
  constructor pre-loss-conference-boundary
  field
    deprotonatedSpectraPubliclyCarriedBeforeDeath : Bool
    conferenceAuthorshipProvesExactRawDataCustody : Bool
    conferenceDateEqualsExperimentRunDate : Bool
    conferenceSpectraEqualFinal2025DatasetWithoutCrosswalk : Bool
    preLossScientificContributionToDeprotonatedLaneSupported : Bool

canonicalPreLossConferenceBoundary : PreLossConferenceBoundary
canonicalPreLossConferenceBoundary =
  pre-loss-conference-boundary true false false false true

------------------------------------------------------------------------
-- Apparatus-host and affiliation provenance.
--
-- JPL's FY23 SURP poster says the collaboration with Weber's team enabled the
-- investigation with an active apparatus and labels the cryogenic IR action-
-- spectroscopy setup as located at Boulder. This pays a public apparatus-host
-- location, not legal ownership, notebook custody, raw-data custody, or a
-- person-specific handover. The ChemRxiv manuscript and 2024 ISMS abstract
-- explicitly affiliate Maiwald with JPL/Caltech, while current ACS/PubMed
-- rendered metadata maps him to JILA/CU Boulder. Preserve the disagreement
-- rather than using one manifestation to overwrite another.
------------------------------------------------------------------------

record ApparatusHostReceipt : Set where
  constructor apparatus-host-receipt
  field
    sourceObject : String
    apparatusDescription : String
    publicHostLocation : String
    collaborationCarrier : String
    apparatusHostLocationPaid : Bool
    legalOwnershipPaid : Bool
    rawDataCustodyPaid : Bool
    notebookCustodyPaid : Bool
    maiwaldPhysicalCustodyPaid : Bool

open ApparatusHostReceipt public

fy23BoulderApparatusHost : ApparatusHostReceipt
fy23BoulderApparatusHost = apparatus-host-receipt
  "JPL FY23 SURP poster SP23012p / CL#23-5018"
  "active messenger-photodissociation action-spectroscopy apparatus including electrospray ionization, cryogenic quadrupole trap and coherent radiation sources"
  "Boulder university / Weber-group collaboration surface"
  "JPL SURP collaboration with J. Mathias Weber team; Lane Terry and Maddie Klumb named as graduate collaborators"
  true false false false false

record AffiliationManifestationDiscrepancy : Set where
  constructor affiliation-manifestation-discrepancy
  field
    objectTitle : String
    doi : String
    chemRxivAffiliation : String
    conferenceAffiliation : String
    acsRenderedAffiliation : String
    pubmedRenderedAffiliation : String
    exactAuthorIdentityPaid : Bool
    exactPublicationIdentityPaid : Bool
    affiliationMetadataConsistentAcrossManifestations : Bool
    affiliationDifferenceMayDetermineApparatusCustody : Bool
    explicitNumberedManuscriptAffiliationMayGuideResolution : Bool

open AffiliationManifestationDiscrepancy public

protonatedValineMaiwaldAffiliationDiscrepancy : AffiliationManifestationDiscrepancy
protonatedValineMaiwaldAffiliationDiscrepancy = affiliation-manifestation-discrepancy
  "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects"
  "10.1021/acs.jpca.4c03552"
  "ChemRxiv PDF: Frank Maiwald affiliation 2 = Jet Propulsion Laboratory, California Institute of Technology"
  "2024 ISMS abstract: Frank Maiwald = Jet Propulsion Laboratory, California Institute of Technology"
  "current ACS rendered author page maps Frank Maiwald to JILA and Department of Chemistry, University of Colorado Boulder"
  "current PubMed rendered metadata maps Frank Maiwald to affiliation 1 = JILA and Department of Chemistry, University of Colorado Boulder"
  true true false false true

------------------------------------------------------------------------
-- ACS SUPPORTING-INFORMATION PRODUCT SURFACES
------------------------------------------------------------------------

record SupportingInformationReceipt : Set where
  constructor supporting-information-receipt
  field
    parentDOI : String
    productDescription : String
    authorshipIncludesMaiwald : Bool
    exactPublicSIObjectLocated : Bool
    rawInstrumentDatasetIncluded : Bool
    exactIdentityWith2023PosterProductsPaid : Bool
    usefulForProductLevelCrosswalk : Bool

open SupportingInformationReceipt public

protonated2024SupportingInformation : SupportingInformationReceipt
protonated2024SupportingInformation = supporting-information-receipt
  "10.1021/acs.jpca.4c03552"
  "calculated IR spectra/isomers; tagged-complex structures; IR photodissociation times; atomic coordinates; unscaled vibrational frequencies"
  true true false false true

deprotonated2025SupportingInformation : SupportingInformationReceipt
deprotonated2025SupportingInformation = supporting-information-receipt
  "10.1021/acs.jpca.5c03141"
  "calculated IR spectra/isomers; N2-tagged [Val-H]- structure/spectra; detailed aminovaleric conformer search including 12 lowest-energy conformers; anharmonic NH/OCO calculations; visual spectral comparison; atomic coordinates"
  false true false false true

record SupportingInformationBoundary : Set where
  constructor supporting-information-boundary
  field publicSIDerivativeEqualsRawData : Bool; publicSIProductsEqual2023PosterProductsWithoutCrosswalk : Bool; laterSIOmissionOfMaiwaldProvesNoPreLossContribution : Bool; SIProductClassesSharpenVersionSearch : Bool

canonicalSupportingInformationBoundary : SupportingInformationBoundary
canonicalSupportingInformationBoundary = supporting-information-boundary false false false true

------------------------------------------------------------------------
-- Temporal split around Maiwald's death on 2024-07-04.
------------------------------------------------------------------------

record ManuscriptChronologyBoundary : Set where
  constructor manuscript-chronology-boundary
  field maiwaldDeathDate : String; protonatedReceivedBeforeDeath : Bool; protonatedRevisedAfterDeath : Bool; protonatedAcceptedAfterDeath : Bool; protonatedRetainedMaiwaldAuthorship : Bool; deprotonatedReceivedAfterDeath : Bool; deprotonatedOmitsMaiwald : Bool; preDeathSubmissionImpliesAllExperimentsPreDeath : Bool; postDeathRevisionImpliesPostDeathScientificContributionByMaiwald : Bool; laterOmissionImpliesCarrierTransfer : Bool
canonicalManuscriptChronologyBoundary = manuscript-chronology-boundary "2024-07-04" true true true true true true false false false

record WorkingTitleScopeFork : Set where
  constructor working-title-scope-fork
  field broadWorkingTitleOwned : Bool; protonatedChildPublished : Bool; deprotonatedChildPublished : Bool; maiwaldRetainedOn2024Child : Bool; maiwaldRetainedOn2025Child : Bool; laterChildWithoutMaiwaldProvesCalibrationTransfer : Bool; laterChildWithoutMaiwaldProvesNoMaiwaldContribution : Bool; scopeForkMayGuideSameCarrierTransferSearch : Bool
canonicalWorkingTitleScopeFork = working-title-scope-fork true true true true false false false true

record ProjectVsCarrierBoundary : Set where
  constructor project-vs-carrier-boundary
  field projectSuccessionImpliesCalibrationTransferred : Bool; projectSuccessionImpliesCalibrationTransferredIsFalse : projectSuccessionImpliesCalibrationTransferred ≡ false; successorPIImpliesSameTacitKnowledge : Bool; successorPIImpliesSameTacitKnowledgeIsFalse : successorPIImpliesSameTacitKnowledge ≡ false; overlappingTeamSupportsContinuitySearch : Bool; overlappingTeamSupportsContinuitySearchIsTrue : overlappingTeamSupportsContinuitySearch ≡ true; publicationContinuationImpliesSameApplicationCarrierTransferred : Bool; publicationContinuationImpliesSameApplicationCarrierTransferredIsFalse : publicationContinuationImpliesSameApplicationCarrierTransferred ≡ false
canonicalProjectVsCarrierBoundary = project-vs-carrier-boundary false refl false refl true refl false refl

data MaiwaldSuccessionReverseTarget : Set where
  acquireApparatusConfigurationContinuity acquireCalibrationTransfer acquireTagResponseModelContinuity acquireFailureHistoryTransfer acquireQualificationTransfer acquireRepositoryOrNotebookContinuity acquireWorkingTitleToPublishedVersionHistory acquireExperimentAndDataProductionDates acquirePreprintAcceptedManuscriptVersionCrosswalk acquireExactDatasetAndReductionVersionCrosswalk acquirePosterToSIProductCrosswalk acquireApparatusOwnershipAndCustodyCrosswalk acquireAffiliationManifestationResolution : MaiwaldSuccessionReverseTarget

manuscriptForkNextTarget : MaiwaldSuccessionReverseTarget
manuscriptForkNextTarget = acquireExactDatasetAndReductionVersionCrosswalk
