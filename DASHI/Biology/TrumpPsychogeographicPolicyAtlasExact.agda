module DASHI.Biology.TrumpPsychogeographicPolicyAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.PsychogeographicFieldExact as Field

------------------------------------------------------------------------
-- Trump-policy psychogeographic atlas.
--
-- Each row is a bounded, source-scoped case surface.  The atlas records how
-- policy can reorganise bodies, homes, routes, civic interfaces, institutions
-- and historical narratives.  It does not decide legality, motive, empirical
-- effect, ideology, or political merit.
------------------------------------------------------------------------

data TrumpPolicyCase : Set where
  immigrationRaidsMassDeportationCase : TrumpPolicyCase
  borderWallCase : TrumpPolicyCase
  januarySixCase : TrumpPolicyCase
  electionDenialCase : TrumpPolicyCase
  presidentialImmunityCase : TrumpPolicyCase
  unitaryExecutiveTheoryCase : TrumpPolicyCase
  christianNationalismInterfaceCase : TrumpPolicyCase
  tariffIndustrialPolicyCase : TrumpPolicyCase
  transPolicyCase : TrumpPolicyCase
  palestinePolicyCase : TrumpPolicyCase
  indigenousPolicyCase : TrumpPolicyCase
  administrativeStateRestructuringCase : TrumpPolicyCase
  palantirSurveillanceProcurementCase : TrumpPolicyCase

canonicalTrumpPolicyCases : List TrumpPolicyCase
canonicalTrumpPolicyCases =
  immigrationRaidsMassDeportationCase
  ∷ borderWallCase
  ∷ januarySixCase
  ∷ electionDenialCase
  ∷ presidentialImmunityCase
  ∷ unitaryExecutiveTheoryCase
  ∷ christianNationalismInterfaceCase
  ∷ tariffIndustrialPolicyCase
  ∷ transPolicyCase
  ∷ palestinePolicyCase
  ∷ indigenousPolicyCase
  ∷ administrativeStateRestructuringCase
  ∷ palantirSurveillanceProcurementCase
  ∷ []

data SpatialCarrier : Set where
  homeWorkplaceSanctuaryCarrier : SpatialCarrier
  borderWallCheckpointCarrier : SpatialCarrier
  capitolPublicAssemblyCarrier : SpatialCarrier
  ballotCertificationCarrier : SpatialCarrier
  presidentialOfficeCourtCarrier : SpatialCarrier
  executiveAgencyCarrier : SpatialCarrier
  churchSchoolPublicSquareCarrier : SpatialCarrier
  portFactorySupplyChainCarrier : SpatialCarrier
  bodyDocumentInstitutionCarrier : SpatialCarrier
  aidCorridorDiplomaticForumCarrier : SpatialCarrier
  countryFederalLandToponymCarrier : SpatialCarrier
  civilServiceRegulatoryCarrier : SpatialCarrier
  dataPlatformCaseManagementCarrier : SpatialCarrier

data PolicyMechanism : Set where
  raidDetentionRemovalMechanism : PolicyMechanism
  wallBarrierPatrolMechanism : PolicyMechanism
  assemblyBreachClemencyMemoryMechanism : PolicyMechanism
  resultContestCertificationMechanism : PolicyMechanism
  officialActImmunityMechanism : PolicyMechanism
  presidentialSupervisionMechanism : PolicyMechanism
  faithStateInterfaceMechanism : PolicyMechanism
  tariffIndustrialReorientationMechanism : PolicyMechanism
  sexClassificationAdministrationMechanism : PolicyMechanism
  aidSanctionsDiplomaticAlignmentMechanism : PolicyMechanism
  landNamingExtractionConsultationMechanism : PolicyMechanism
  workforceDeregulationAgencyReductionMechanism : PolicyMechanism
  dataIntegrationVendorProcurementMechanism : PolicyMechanism

data AffectedPosition : Set where
  migrantPosition : AffectedPosition
  mixedStatusFamilyPosition : AffectedPosition
  borderCommunityPosition : AffectedPosition
  protesterPosition : AffectedPosition
  electionWorkerPosition : AffectedPosition
  voterPosition : AffectedPosition
  presidentPosition : AffectedPosition
  civilServantPosition : AffectedPosition
  faithCommunityPosition : AffectedPosition
  nonChristianCommunityPosition : AffectedPosition
  workerProducerConsumerPosition : AffectedPosition
  transPersonPosition : AffectedPosition
  palestinianCivilianPosition : AffectedPosition
  israeliCivilianPosition : AffectedPosition
  indigenousNationPosition : AffectedPosition
  dataSubjectPosition : AffectedPosition
  contractorPosition : AffectedPosition

record PolicySource : Set where
  constructor policySource
  field
    sourceInstitution : String
    sourceTitle : String
    sourceDate : String
    sourceIdentifier : String
    importedRole : String
    sourceCreatesLegalConclusion : Bool
    sourceCreatesPolicyEndorsement : Bool

open PolicySource public

mkPolicySource : String → String → String → String → String → PolicySource
mkPolicySource institution title date identifier role =
  policySource institution title date identifier role false false

securingOurBordersSource : PolicySource
securingOurBordersSource =
  mkPolicySource
    "White House"
    "Securing Our Borders"
    "2025-01-20"
    "Executive Order 14165"
    "border wall, detention, removal, personnel and technology policy source"

southernBorderEmergencySource : PolicySource
southernBorderEmergencySource =
  mkPolicySource
    "White House"
    "Declaring a National Emergency at the Southern Border"
    "2025-01-20"
    "Proclamation 10886"
    "border emergency, military support and threat-narrative source"

januarySixReportSource : PolicySource
januarySixReportSource =
  mkPolicySource
    "U.S. House Select Committee / Government Publishing Office"
    "Final Report of the Select Committee to Investigate the January 6th Attack"
    "2022-12-22"
    "H. Rept. 117-663"
    "congressional account of election-result contest and Capitol attack"

januarySixClemencySource : PolicySource
januarySixClemencySource =
  mkPolicySource
    "White House"
    "Granting Pardons and Commutation for Certain January 6 Offenses"
    "2025-01-20"
    "presidential proclamation"
    "clemency and public-memory reclassification source"

presidentialImmunitySource : PolicySource
presidentialImmunitySource =
  mkPolicySource
    "Supreme Court of the United States"
    "Trump v. United States"
    "2024-07-01"
    "603 U.S. 593"
    "official-act immunity doctrine source; scope remains legal and source-specific"

independentAgencySource : PolicySource
independentAgencySource =
  mkPolicySource
    "White House"
    "Ensuring Accountability for All Agencies"
    "2025-02-18"
    "Executive Order 14215"
    "presidential supervision of independent-agency policy and review"

policyCareerSource : PolicySource
policyCareerSource =
  mkPolicySource
    "White House"
    "Restoring Accountability to Policy-Influencing Positions Within the Federal Workforce"
    "2025-01-20"
    "Executive Order 14171"
    "civil-service reclassification and presidential-control source"

faithOfficeSource : PolicySource
faithOfficeSource =
  mkPolicySource
    "White House"
    "Establishment of the White House Faith Office"
    "2025-02-07"
    "Executive Order 14205"
    "faith-based institution, funding and executive-policy interface source"

tradePolicySource : PolicySource
tradePolicySource =
  mkPolicySource
    "White House"
    "America First Trade Policy"
    "2025-01-20"
    "presidential memorandum"
    "tariff, supply-chain, industrial and economic-security source"

sexClassificationSource : PolicySource
sexClassificationSource =
  mkPolicySource
    "White House"
    "Defending Women from Gender Ideology Extremism and Restoring Biological Truth"
    "2025-01-20"
    "Executive Order 14168"
    "federal sex-classification, document and programme-administration source"

palestineUNSource : PolicySource
palestineUNSource =
  mkPolicySource
    "White House"
    "Withdrawing from and Ending Funding to Certain United Nations Organizations"
    "2025-02-04"
    "Executive Order 14199"
    "UNRWA funding and international-organisation policy source"

palestineICCSource : PolicySource
palestineICCSource =
  mkPolicySource
    "White House"
    "Imposing Sanctions on the International Criminal Court"
    "2025-02-06"
    "Executive Order 14203"
    "ICC sanctions and United States-Israel alignment source"

alaskaResourceSource : PolicySource
alaskaResourceSource =
  mkPolicySource
    "White House"
    "Unleashing Alaska's Extraordinary Resource Potential"
    "2025-01-20"
    "Executive Order 14153"
    "Alaska land, extraction, Native-land review and sacred-site policy source"

restoringNamesSource : PolicySource
restoringNamesSource =
  mkPolicySource
    "White House"
    "Restoring Names That Honor American Greatness"
    "2025-01-20"
    "Executive Order 14172"
    "federal toponym and national-memory source"

informationSilosSource : PolicySource
informationSilosSource =
  mkPolicySource
    "White House"
    "Stopping Waste, Fraud, and Abuse by Eliminating Information Silos"
    "2025-03-20"
    "Executive Order 14243"
    "inter-agency data access and consolidation source"

palantirAwardSource : PolicySource
palantirAwardSource =
  mkPolicySource
    "USAspending / Department of Homeland Security"
    "Homeland Security Investigations case-management and analytics modernization"
    "2026-06-26"
    "PIID 70CTD026FC0000018"
    "bounded procurement record for Palantir Technologies; no abuse inference"

record PolicyCaseSurface : Set where
  constructor policyCaseSurface
  field
    policyCase : TrumpPolicyCase
    caseLabel : String
    primaryScale : Field.SpatialScale
    primaryCarrier : SpatialCarrier
    mechanism : PolicyMechanism
    affectedPositions : List AffectedPosition
    sources : List PolicySource
    externalEvidenceRequired : Bool
    legalStatusMayChange : Bool
    observerPluralityRequired : Bool
    formalCaseCreatesLegalConclusion : Bool
    formalCaseCreatesPoliticalAuthority : Bool

open PolicyCaseSurface public

mkPolicyCaseSurface :
  TrumpPolicyCase →
  String →
  Field.SpatialScale →
  SpatialCarrier →
  PolicyMechanism →
  List AffectedPosition →
  List PolicySource →
  PolicyCaseSurface
mkPolicyCaseSurface c label scale carrier mech positions refs =
  policyCaseSurface
    c label scale carrier mech positions refs
    true true true false false

immigrationRaidsMassDeportationSurface : PolicyCaseSurface
immigrationRaidsMassDeportationSurface =
  mkPolicyCaseSurface
    immigrationRaidsMassDeportationCase
    "immigration raids, detention and mass-removal programme"
    Field.intimateLocalityScale
    homeWorkplaceSanctuaryCarrier
    raidDetentionRemovalMechanism
    (migrantPosition ∷ mixedStatusFamilyPosition ∷ dataSubjectPosition ∷ [])
    (securingOurBordersSource ∷ southernBorderEmergencySource ∷ [])

borderWallSurface : PolicyCaseSurface
borderWallSurface =
  mkPolicyCaseSurface
    borderWallCase
    "southern-border wall, barrier, patrol and military-support field"
    Field.streetThresholdScale
    borderWallCheckpointCarrier
    wallBarrierPatrolMechanism
    (migrantPosition ∷ borderCommunityPosition ∷ indigenousNationPosition ∷ [])
    (securingOurBordersSource ∷ southernBorderEmergencySource ∷ [])

januarySixSurface : PolicyCaseSurface
januarySixSurface =
  mkPolicyCaseSurface
    januarySixCase
    "January 6 Capitol attack, assembly route, prosecution and clemency memory field"
    Field.civicInterfaceScale
    capitolPublicAssemblyCarrier
    assemblyBreachClemencyMemoryMechanism
    (protesterPosition ∷ electionWorkerPosition ∷ voterPosition ∷ [])
    (januarySixReportSource ∷ januarySixClemencySource ∷ [])

electionDenialSurface : PolicyCaseSurface
electionDenialSurface =
  mkPolicyCaseSurface
    electionDenialCase
    "election-result denial, certification pressure and institutional trust field"
    Field.historicalHorizonScale
    ballotCertificationCarrier
    resultContestCertificationMechanism
    (electionWorkerPosition ∷ voterPosition ∷ civilServantPosition ∷ [])
    (januarySixReportSource ∷ [])

presidentialImmunitySurface : PolicyCaseSurface
presidentialImmunitySurface =
  mkPolicyCaseSurface
    presidentialImmunityCase
    "presidential official-act immunity and accountability boundary"
    Field.civicInterfaceScale
    presidentialOfficeCourtCarrier
    officialActImmunityMechanism
    (presidentPosition ∷ voterPosition ∷ civilServantPosition ∷ [])
    (presidentialImmunitySource ∷ [])

unitaryExecutiveTheorySurface : PolicyCaseSurface
unitaryExecutiveTheorySurface =
  mkPolicyCaseSurface
    unitaryExecutiveTheoryCase
    "unitary-executive supervision of agencies and legal interpretation"
    Field.districtOrganisationScale
    executiveAgencyCarrier
    presidentialSupervisionMechanism
    (presidentPosition ∷ civilServantPosition ∷ voterPosition ∷ [])
    (independentAgencySource ∷ policyCareerSource ∷ [])

christianNationalismInterfaceSurface : PolicyCaseSurface
christianNationalismInterfaceSurface =
  mkPolicyCaseSurface
    christianNationalismInterfaceCase
    "Christian-nationalism candidate interface with faith-office and public-policy infrastructure"
    Field.historicalHorizonScale
    churchSchoolPublicSquareCarrier
    faithStateInterfaceMechanism
    (faithCommunityPosition ∷ nonChristianCommunityPosition ∷ voterPosition ∷ [])
    (faithOfficeSource ∷ [])

tariffIndustrialPolicySurface : PolicyCaseSurface
tariffIndustrialPolicySurface =
  mkPolicyCaseSurface
    tariffIndustrialPolicyCase
    "tariff, industrial reorientation, port and supply-chain geography"
    Field.districtOrganisationScale
    portFactorySupplyChainCarrier
    tariffIndustrialReorientationMechanism
    (workerProducerConsumerPosition ∷ contractorPosition ∷ [])
    (tradePolicySource ∷ [])

transPolicySurface : PolicyCaseSurface
transPolicySurface =
  mkPolicyCaseSurface
    transPolicyCase
    "federal trans-policy classification across bodies, documents and institutions"
    Field.bodyFootingScale
    bodyDocumentInstitutionCarrier
    sexClassificationAdministrationMechanism
    (transPersonPosition ∷ civilServantPosition ∷ dataSubjectPosition ∷ [])
    (sexClassificationSource ∷ [])

palestinePolicySurface : PolicyCaseSurface
palestinePolicySurface =
  mkPolicyCaseSurface
    palestinePolicyCase
    "United States Palestine-policy lane across aid, sanctions and diplomatic institutions"
    Field.historicalHorizonScale
    aidCorridorDiplomaticForumCarrier
    aidSanctionsDiplomaticAlignmentMechanism
    (palestinianCivilianPosition ∷ israeliCivilianPosition ∷ voterPosition ∷ [])
    (palestineUNSource ∷ palestineICCSource ∷ [])

indigenousPolicySurface : PolicyCaseSurface
indigenousPolicySurface =
  mkPolicyCaseSurface
    indigenousPolicyCase
    "Indigenous sovereignty, federal land, extraction, consultation and naming lane"
    Field.historicalHorizonScale
    countryFederalLandToponymCarrier
    landNamingExtractionConsultationMechanism
    (indigenousNationPosition ∷ workerProducerConsumerPosition ∷ voterPosition ∷ [])
    (alaskaResourceSource ∷ restoringNamesSource ∷ [])

administrativeStateRestructuringSurface : PolicyCaseSurface
administrativeStateRestructuringSurface =
  mkPolicyCaseSurface
    administrativeStateRestructuringCase
    "administrative-state workforce, deregulation and agency-reduction lane"
    Field.districtOrganisationScale
    civilServiceRegulatoryCarrier
    workforceDeregulationAgencyReductionMechanism
    (civilServantPosition ∷ voterPosition ∷ workerProducerConsumerPosition ∷ [])
    (policyCareerSource ∷ independentAgencySource ∷ [])

palantirSurveillanceProcurementSurface : PolicyCaseSurface
palantirSurveillanceProcurementSurface =
  mkPolicyCaseSurface
    palantirSurveillanceProcurementCase
    "Palantir or comparable vendor-mediated surveillance and case-management procurement"
    Field.districtOrganisationScale
    dataPlatformCaseManagementCarrier
    dataIntegrationVendorProcurementMechanism
    (dataSubjectPosition ∷ migrantPosition ∷ civilServantPosition ∷ contractorPosition ∷ [])
    (informationSilosSource ∷ palantirAwardSource ∷ [])

canonicalPolicyCaseSurfaces : List PolicyCaseSurface
canonicalPolicyCaseSurfaces =
  immigrationRaidsMassDeportationSurface
  ∷ borderWallSurface
  ∷ januarySixSurface
  ∷ electionDenialSurface
  ∷ presidentialImmunitySurface
  ∷ unitaryExecutiveTheorySurface
  ∷ christianNationalismInterfaceSurface
  ∷ tariffIndustrialPolicySurface
  ∷ transPolicySurface
  ∷ palestinePolicySurface
  ∷ indigenousPolicySurface
  ∷ administrativeStateRestructuringSurface
  ∷ palantirSurveillanceProcurementSurface
  ∷ []

------------------------------------------------------------------------
-- Shared projection grammar adapted from the Cabarlah/trauma bridge in PR 450.
-- It is a candidate descriptive shape, not a causal equivalence theorem.
------------------------------------------------------------------------

data PolicyProjectionStage : Set where
  selectedInjuryThreatOrDefectStage : PolicyProjectionStage
  compressedExternalCarrierStage : PolicyProjectionStage
  mobilisedSpatialInfrastructureStage : PolicyProjectionStage

nextPolicyProjectionStage : PolicyProjectionStage → PolicyProjectionStage
nextPolicyProjectionStage selectedInjuryThreatOrDefectStage =
  compressedExternalCarrierStage
nextPolicyProjectionStage compressedExternalCarrierStage =
  mobilisedSpatialInfrastructureStage
nextPolicyProjectionStage mobilisedSpatialInfrastructureStage =
  mobilisedSpatialInfrastructureStage

candidateProjectionReachesSpatialMobilisation :
  nextPolicyProjectionStage
    (nextPolicyProjectionStage selectedInjuryThreatOrDefectStage)
  ≡ mobilisedSpatialInfrastructureStage
candidateProjectionReachesSpatialMobilisation = refl

record TrumpPolicyAtlasBoundary : Set where
  constructor trumpPolicyAtlasBoundary
  field
    onePolicyCaseRepresentsWholeAdministration : Bool
    onePolicyCaseRepresentsWholeAdministrationIsFalse :
      onePolicyCaseRepresentsWholeAdministration ≡ false
    sharedProjectionShapeMakesCasesHistoricallyEquivalent : Bool
    sharedProjectionShapeMakesCasesHistoricallyEquivalentIsFalse :
      sharedProjectionShapeMakesCasesHistoricallyEquivalent ≡ false
    officialSourceTextSettlesLegality : Bool
    officialSourceTextSettlesLegalityIsFalse :
      officialSourceTextSettlesLegality ≡ false
    procurementRecordProvesSurveillanceAbuse : Bool
    procurementRecordProvesSurveillanceAbuseIsFalse :
      procurementRecordProvesSurveillanceAbuse ≡ false
    faithStateInterfaceEqualsChristianNationalism : Bool
    faithStateInterfaceEqualsChristianNationalismIsFalse :
      faithStateInterfaceEqualsChristianNationalism ≡ false
    federalLandTitleErasesIndigenousCountry : Bool
    federalLandTitleErasesIndigenousCountryIsFalse :
      federalLandTitleErasesIndigenousCountry ≡ false

canonicalTrumpPolicyAtlasBoundary : TrumpPolicyAtlasBoundary
canonicalTrumpPolicyAtlasBoundary =
  trumpPolicyAtlasBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
