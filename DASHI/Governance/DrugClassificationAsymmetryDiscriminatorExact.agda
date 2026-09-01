module DASHI.Governance.DrugClassificationAsymmetryDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Governance.DrugGovernanceIntersectionalAuthorityExact as Intersectional
import DASHI.Governance.WarOnDrugsHistoricalGenealogyExact as Genealogy

------------------------------------------------------------------------
-- CARE VS PUNISHMENT CLASSIFICATION ASYMMETRY
--
-- Which coordinates change the reachable governance route when the broad
-- psychoactive/drug surface is held fixed?  This owner turns that question into
-- an explicit discriminator problem.  Synthetic worlds are used only to make
-- the geometry exact; no empirical disparity magnitude is asserted here.
------------------------------------------------------------------------

data VeteranStatus : Set where
  veteran
  nonVeteran
  : VeteranStatus

data RacializedPosition : Set where
  racializedMinorityPosition
  majorityPosition
  unspecifiedRacializedPosition
  : RacializedPosition

data ClassHousingPosition : Set where
  housedSecure
  precariouslyHoused
  unhoused
  classHousingUnspecified
  : ClassHousingPosition

data MedicalDiagnosisStatus : Set where
  qualifyingDiagnosis
  noQualifyingDiagnosis
  diagnosisUnspecified
  : MedicalDiagnosisStatus

data CommercialSponsorship : Set where
  sponsoredClinicalProgram
  commercialProductSponsor
  noSponsor
  : CommercialSponsorship

data IndigenousSovereigntyStatus : Set where
  indigenousSovereignProtocol
  externalNonIndigenousRoute
  sovereigntyUnspecified
  : IndigenousSovereigntyStatus

data DrugIdentityClass : Set where
  psilocybinClass
  mdmaClass
  cannabisClass
  opioidClass
  stimulantClass
  unspecifiedDrugClass
  : DrugIdentityClass

data InstitutionalSetting : Set where
  vaClinicalSetting
  fdaRegulatedTrialSetting
  ordinaryMedicalSetting
  commercialMarketSetting
  streetPolicingSetting
  indigenousCeremonialSetting
  : InstitutionalSetting

data GovernanceCone : Set where
  careResearchCone
  regulatedMedicalCone
  commercialAccessCone
  punitiveSecurityCone
  sovereignCeremonialCone
  mixedOrUnresolvedCone
  : GovernanceCone

record ClassificationWorld : Set where
  constructor classificationWorld
  field
    veteranStatus : VeteranStatus
    racializedPosition : RacializedPosition
    classHousing : ClassHousingPosition
    diagnosis : MedicalDiagnosisStatus
    sponsorship : CommercialSponsorship
    sovereignty : IndigenousSovereigntyStatus
    drugIdentity : DrugIdentityClass
    institutionalSetting : InstitutionalSetting
    route : GovernanceCone

open ClassificationWorld public

------------------------------------------------------------------------
-- Canonical synthetic worlds.  They are deliberately matched on psilocybin
-- identity while varying veteran/diagnosis/institutional route.
------------------------------------------------------------------------

veteranClinicalWorld : ClassificationWorld
veteranClinicalWorld = classificationWorld
  veteran
  unspecifiedRacializedPosition
  housedSecure
  qualifyingDiagnosis
  sponsoredClinicalProgram
  externalNonIndigenousRoute
  psilocybinClass
  vaClinicalSetting
  careResearchCone

nonVeteranPolicingWorld : ClassificationWorld
nonVeteranPolicingWorld = classificationWorld
  nonVeteran
  unspecifiedRacializedPosition
  classHousingUnspecified
  noQualifyingDiagnosis
  noSponsor
  externalNonIndigenousRoute
  psilocybinClass
  streetPolicingSetting
  punitiveSecurityCone

indigenousCeremonialWorld : ClassificationWorld
indigenousCeremonialWorld = classificationWorld
  nonVeteran
  unspecifiedRacializedPosition
  classHousingUnspecified
  diagnosisUnspecified
  noSponsor
  indigenousSovereignProtocol
  psilocybinClass
  indigenousCeremonialSetting
  sovereignCeremonialCone

------------------------------------------------------------------------
-- Existing coarse observer deliberately sees only the broad drug identity.
------------------------------------------------------------------------

coarseDrugObserver : ClassificationWorld → DrugIdentityClass
coarseDrugObserver = drugIdentity

veteranAndPolicingCollapse :
  coarseDrugObserver veteranClinicalWorld ≡
  coarseDrugObserver nonVeteranPolicingWorld
veteranAndPolicingCollapse = refl

veteranAndIndigenousCollapse :
  coarseDrugObserver veteranClinicalWorld ≡
  coarseDrugObserver indigenousCeremonialWorld
veteranAndIndigenousCollapse = refl

routeDiffersVeteranPolicing :
  route veteranClinicalWorld ≡ route nonVeteranPolicingWorld → ⊥
routeDiffersVeteranPolicing ()

routeDiffersVeteranIndigenous :
  route veteranClinicalWorld ≡ route indigenousCeremonialWorld → ⊥
routeDiffersVeteranIndigenous ()

------------------------------------------------------------------------
-- Candidate discriminator coordinates.
------------------------------------------------------------------------

data ClassificationCoordinate : Set where
  veteranCoordinate
  racializedPositionCoordinate
  classHousingCoordinate
  diagnosisCoordinate
  sponsorshipCoordinate
  sovereigntyCoordinate
  drugIdentityCoordinate
  institutionalSettingCoordinate
  : ClassificationCoordinate

data CoordinateValue : Set where
  veteranValue nonVeteranValue
  racializedMinorityValue majorityValue racializedUnknownValue
  housedValue precariousValue unhousedValue housingUnknownValue
  qualifyingDiagnosisValue noDiagnosisValue diagnosisUnknownValue
  sponsoredClinicalValue commercialSponsorValue noSponsorValue
  indigenousSovereignValue externalRouteValue sovereigntyUnknownValue
  psilocybinValue mdmaValue cannabisValue opioidValue stimulantValue drugUnknownValue
  vaSettingValue fdaSettingValue ordinaryMedicalValue commercialMarketValue streetPolicingValue indigenousCeremonialValue
  : CoordinateValue

readCoordinate : ClassificationCoordinate → ClassificationWorld → CoordinateValue
readCoordinate veteranCoordinate world with veteranStatus world
... | veteran = veteranValue
... | nonVeteran = nonVeteranValue
readCoordinate racializedPositionCoordinate world with racializedPosition world
... | racializedMinorityPosition = racializedMinorityValue
... | majorityPosition = majorityValue
... | unspecifiedRacializedPosition = racializedUnknownValue
readCoordinate classHousingCoordinate world with classHousing world
... | housedSecure = housedValue
... | precariouslyHoused = precariousValue
... | unhoused = unhousedValue
... | classHousingUnspecified = housingUnknownValue
readCoordinate diagnosisCoordinate world with diagnosis world
... | qualifyingDiagnosis = qualifyingDiagnosisValue
... | noQualifyingDiagnosis = noDiagnosisValue
... | diagnosisUnspecified = diagnosisUnknownValue
readCoordinate sponsorshipCoordinate world with sponsorship world
... | sponsoredClinicalProgram = sponsoredClinicalValue
... | commercialProductSponsor = commercialSponsorValue
... | noSponsor = noSponsorValue
readCoordinate sovereigntyCoordinate world with sovereignty world
... | indigenousSovereignProtocol = indigenousSovereignValue
... | externalNonIndigenousRoute = externalRouteValue
... | sovereigntyUnspecified = sovereigntyUnknownValue
readCoordinate drugIdentityCoordinate world with drugIdentity world
... | psilocybinClass = psilocybinValue
... | mdmaClass = mdmaValue
... | cannabisClass = cannabisValue
... | opioidClass = opioidValue
... | stimulantClass = stimulantValue
... | unspecifiedDrugClass = drugUnknownValue
readCoordinate institutionalSettingCoordinate world with institutionalSetting world
... | vaClinicalSetting = vaSettingValue
... | fdaRegulatedTrialSetting = fdaSettingValue
... | ordinaryMedicalSetting = ordinaryMedicalValue
... | commercialMarketSetting = commercialMarketValue
... | streetPolicingSetting = streetPolicingValue
... | indigenousCeremonialSetting = indigenousCeremonialValue

coordinateBundle : ClassificationCoordinate → Discriminator.ExperimentBundle ClassificationWorld
coordinateBundle coordinate = Discriminator.experimentBundle
  CoordinateValue
  (readCoordinate coordinate)
  (suc zero)
  "classification-coordinate observation"
  "synthetic exact discriminator; empirical calibration required before real-world use"

institutionalSettingSeparatesVeteranFromPolicing :
  Discriminator.BundleSeparates
    (coordinateBundle institutionalSettingCoordinate)
    veteranClinicalWorld
    nonVeteranPolicingWorld
institutionalSettingSeparatesVeteranFromPolicing = record
  { separates = λ () }

veteranStatusSeparatesVeteranFromPolicing :
  Discriminator.BundleSeparates
    (coordinateBundle veteranCoordinate)
    veteranClinicalWorld
    nonVeteranPolicingWorld
veteranStatusSeparatesVeteranFromPolicing = record
  { separates = λ () }

sovereigntySeparatesVeteranFromIndigenous :
  Discriminator.BundleSeparates
    (coordinateBundle sovereigntyCoordinate)
    veteranClinicalWorld
    indigenousCeremonialWorld
sovereigntySeparatesVeteranFromIndigenous = record
  { separates = λ () }

------------------------------------------------------------------------
-- A discriminator can distinguish worlds without proving that the coordinate is
-- the causal reason for the route difference.  Causal mediation remains extra.
------------------------------------------------------------------------

data SeparationPromotesCausalClassificationMechanism : Set where

data VeteranDifferencePromotesVeteranCause : Set where

data RacializedDifferencePromotesRacialDiscriminationCause : Set where

data SettingDifferencePromotesInstitutionalCause : Set where

separationDoesNotPromoteCausalMechanism :
  SeparationPromotesCausalClassificationMechanism → ⊥
separationDoesNotPromoteCausalMechanism ()

veteranDifferenceDoesNotPromoteVeteranCause :
  VeteranDifferencePromotesVeteranCause → ⊥
veteranDifferenceDoesNotPromoteVeteranCause ()

racializedDifferenceDoesNotPromoteDiscriminationCause :
  RacializedDifferencePromotesRacialDiscriminationCause → ⊥
racializedDifferenceDoesNotPromoteDiscriminationCause ()

settingDifferenceDoesNotPromoteInstitutionalCause :
  SettingDifferencePromotesInstitutionalCause → ⊥
settingDifferenceDoesNotPromoteInstitutionalCause ()

------------------------------------------------------------------------
-- Historical counterculture becomes another carrier/status comparison axis.
------------------------------------------------------------------------

data HistoricalCarrierPosition : Set where
  hippieCountercultureCarrier
  antiwarYouthCarrier
  blackPoliticalCarrier
  vietnamVeteranCarrier
  contemporaryVeteranClinicalCarrier
  : HistoricalCarrierPosition

historicalGenealogyBoundary : Genealogy.WarOnDrugsHistoricalGenealogyBoundary
historicalGenealogyBoundary = Genealogy.canonicalWarOnDrugsHistoricalGenealogyBoundary

intersectionalBoundary : Intersectional.DrugGovernanceIntersectionalBoundary
intersectionalBoundary = Intersectional.canonicalDrugGovernanceIntersectionalBoundary

record DrugClassificationAsymmetryBoundary : Set where
  constructor drugClassificationAsymmetryBoundary
  field
    sameDrugIdentityCanReachDifferentGovernanceCones : Bool
    sameDrugIdentityCanReachDifferentGovernanceConesIsTrue :
      sameDrugIdentityCanReachDifferentGovernanceCones ≡ true
    coordinateMeasurementCanSeparateCollapsedWorlds : Bool
    coordinateMeasurementCanSeparateCollapsedWorldsIsTrue :
      coordinateMeasurementCanSeparateCollapsedWorlds ≡ true
    pairwiseSeparationEstablishesCausalDiscrimination : Bool
    pairwiseSeparationEstablishesCausalDiscriminationIsFalse :
      pairwiseSeparationEstablishesCausalDiscrimination ≡ false
    historicalCountercultureCanBeComparedAsCarrierPosition : Bool
    historicalCountercultureCanBeComparedAsCarrierPositionIsTrue :
      historicalCountercultureCanBeComparedAsCarrierPosition ≡ true
    careVersusPunishmentRequiresMultiaxialComparison : Bool
    careVersusPunishmentRequiresMultiaxialComparisonIsTrue :
      careVersusPunishmentRequiresMultiaxialComparison ≡ true

canonicalDrugClassificationAsymmetryBoundary : DrugClassificationAsymmetryBoundary
canonicalDrugClassificationAsymmetryBoundary =
  drugClassificationAsymmetryBoundary
    true refl
    true refl
    false refl
    true refl
    true refl
