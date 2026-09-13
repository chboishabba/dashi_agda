module DASHI.Law.SensibLawBrightonS185HistoricalAuthoritySourceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.SensibLawOntologyTopology as Ontology

------------------------------------------------------------------------
-- BRIGHTON / RTRA s 185 HISTORICAL SOURCE VERSION
--
-- Public primary-law receipt only.  No private matter evidence lives here.
--
-- Queensland Legislation's reprint table places an Act version effective from
-- 1 October 2022, followed by the next reprint effective 1 March 2023.  The
-- 24 January 2023 Brighton matter date lies inside that version envelope.
--
-- The Act itself did not cease on 1 March 2023: the version/reprint changed.
------------------------------------------------------------------------

rtra2008SourceId : Ontology.StableId
rtra2008SourceId = Ontology.stableId "legal-source:qld:rtra-2008:s185:reprint-2022-10-01"

brightonMatterDate : String
brightonMatterDate = "2023-01-24"

versionEffectiveFrom : String
versionEffectiveFrom = "2022-10-01"

nextVersionEffectiveFrom : String
nextVersionEffectiveFrom = "2023-03-01"

data BrightonMatterDateWithinVersion : Set where
  qldLegislationReprintHistoryWitness : BrightonMatterDateWithinVersion

brightonMatterDateWithinVersion : BrightonMatterDateWithinVersion
brightonMatterDateWithinVersion = qldLegislationReprintHistoryWitness

historicalS185Source : Ontology.StableId → Ontology.LegalSource
historicalS185Source systemId =
  Ontology.legalSource
    rtra2008SourceId
    systemId
    Ontology.statute
    "Residential Tenancies and Rooming Accommodation Act 2008 (Qld), s 185, version effective 1-Oct-2022"
    versionEffectiveFrom
    "next reprint effective 2023-03-01"

record HistoricalS185SourceVersionReceipt (systemId : Ontology.StableId) : Set where
  constructor historical-s185-source-version-receipt
  field
    source : Ontology.LegalSource
    sourceIsExactVersion : source ≡ historicalS185Source systemId
    matterDate : String
    matterDateIs24Jan2023 : matterDate ≡ brightonMatterDate
    reprintEffectiveFrom : String
    reprintEffectiveFromIs1Oct2022 : reprintEffectiveFrom ≡ versionEffectiveFrom
    followingReprintEffectiveFrom : String
    followingReprintEffectiveFromIs1Mar2023 :
      followingReprintEffectiveFrom ≡ nextVersionEffectiveFrom
    matterDateWithinVersion : BrightonMatterDateWithinVersion
    exactProvisionLocator : String
    provisionBoundary : String
    officialPointInTimeReference : String
    officialLegislativeHistoryReference : String
    primaryLegislation : Bool
    primaryLegislationIsTrue : primaryLegislation ≡ true
    sourceVersionReceiptReference : String

open HistoricalS185SourceVersionReceipt public

canonicalHistoricalS185SourceVersionReceipt :
  (systemId : Ontology.StableId) → HistoricalS185SourceVersionReceipt systemId
canonicalHistoricalS185SourceVersionReceipt systemId =
  historical-s185-source-version-receipt
    (historicalS185Source systemId)
    refl
    brightonMatterDate
    refl
    versionEffectiveFrom
    refl
    nextVersionEffectiveFrom
    refl
    brightonMatterDateWithinVersion
    "Residential Tenancies and Rooming Accommodation Act 2008 (Qld) s 185(3)(a)-(b)"
    "while tenancy continues: maintenance duties concerning fitness to live in and good repair; source receipt does not decide matter facts or breach"
    "https://www.legislation.qld.gov.au/view/whole/html/inforce/2022-12-23/act-2008-073"
    "Queensland Legislation table of reprints: 1-Oct-2022 version; next reprint 1-Mar-2023"
    true refl
    "Brighton s185 historical primary-source version receipt v1"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ReprintEndMeansActCeased : Set where
data HistoricalSourceVersionEstablishesMatterFact : Set where
data HistoricalSourceVersionEstablishesBreach : Set where
data SameProvisionLabelProvesSameVersion : Set where
data LaterVersionSubstitutesWithoutTemporalReceipt : Set where

reprintEndDoesNotMeanActCeased : ReprintEndMeansActCeased → ⊥
reprintEndDoesNotMeanActCeased ()

historicalSourceVersionDoesNotEstablishMatterFact :
  HistoricalSourceVersionEstablishesMatterFact → ⊥
historicalSourceVersionDoesNotEstablishMatterFact ()

historicalSourceVersionDoesNotEstablishBreach :
  HistoricalSourceVersionEstablishesBreach → ⊥
historicalSourceVersionDoesNotEstablishBreach ()

sameProvisionLabelDoesNotProveSameVersion :
  SameProvisionLabelProvesSameVersion → ⊥
sameProvisionLabelDoesNotProveSameVersion ()

laterVersionCannotSubstituteWithoutTemporalReceipt :
  LaterVersionSubstitutesWithoutTemporalReceipt → ⊥
laterVersionCannotSubstituteWithoutTemporalReceipt ()

record HistoricalS185SourceVersionBoundary : Set where
  constructor historical-s185-source-version-boundary
  field
    publicPrimarySourceOnly : Bool
    exactVersionIdentityPinned : Bool
    exactMatterDatePinned : Bool
    exactReprintEnvelopePinned : Bool
    exactProvisionLocatorPinned : Bool
    reprintEndMeansActCeased : Bool
    historicalVersionCreatesMatterFact : Bool
    historicalVersionCreatesBreach : Bool
    sameProvisionLabelProvesSameVersion : Bool
    laterVersionMaySubstituteWithoutTemporalReceipt : Bool

canonicalHistoricalS185SourceVersionBoundary : HistoricalS185SourceVersionBoundary
canonicalHistoricalS185SourceVersionBoundary =
  historical-s185-source-version-boundary
    true true true true true
    false false false false false
