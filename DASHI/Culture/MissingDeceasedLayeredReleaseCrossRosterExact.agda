module DASHI.Culture.MissingDeceasedLayeredReleaseCrossRosterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.LayeredKnowledgeReleaseBidiExact as L
import DASHI.Culture.POAMSLayeredReleaseExact as P

------------------------------------------------------------------------
-- CROSS-ROSTER LAYERED RELEASE COMPARISON
--
-- The stronger discriminator is not "public artifact exists" but:
--
--   public report + independently documented bounded/private underlying layer.
--
-- Unknown underlying status remains unresolved and cannot be counted as a
-- documented partial-release boundary.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Joshua LeBlanc / NASA FSP I&C
------------------------------------------------------------------------

leblancGovernance : L.LayerReceipt
leblancGovernance = L.layer-receipt
  "NASA FSP/SNP I&C Technology Development Path"
  L.governanceRestriction
  L.unknown
  "NASA NTRS 20250008475"
  "The public record documents NASA peer review and Public Use Permitted status, but this pass does not establish a prior proprietary/classified/restricted governance state for the same object."

leblancReport : L.LayerReceipt
leblancReport = L.layer-receipt
  "NASA 40 kW Fission Surface Power I&C Technology Development Path"
  L.publicTechnicalReport
  L.public
  "NASA NTRS 20250008475"
  "NASA publicly distributes the presentation; the record states Public Use Permitted and NASA Peer Committee review."

leblancData : L.LayerReceipt
leblancData = L.layer-receipt
  "FSP FICS databases and working technical data"
  L.underlyingData
  L.unknown
  "NASA NTRS 20250008475"
  "The presentation discusses a live FICS database and working groups, but the current public record does not establish whether the complete underlying database is publicly downloadable or privately bounded."

leblancHardware : L.LayerReceipt
leblancHardware = L.layer-receipt
  "FSP/SNP I&C development hardware"
  L.physicalHardware
  L.unknown
  "NASA NTRS 20250008475"
  "The presentation discusses technology maturation; public hardware access is not established."

leblancKnowHow : L.LayerReceipt
leblancKnowHow = L.layer-receipt
  "FSP/SNP I&C implementation know-how"
  L.implementationKnowHow
  L.unknown
  "NASA NTRS 20250008475"
  "Public presentation depth does not establish release of all implementation-specific or tacit know-how."

leblancDerivatives : L.LayerReceipt
leblancDerivatives = L.layer-receipt
  "FSP/SNP later derived technical results"
  L.derivedPrivateResults
  L.unknown
  "NASA NTRS public record inspected to date"
  "No same-object derivative release state is claimed."

leblancLayeredProfile : L.LayeredReleaseProfile
leblancLayeredProfile = L.layered-release-profile
  "Joshua LeBlanc / NASA FSP-SNP I&C"
  leblancGovernance leblancReport leblancData leblancHardware leblancKnowHow leblancDerivatives
  "NASA NTRS 20250008475"

leblancWeakPartial : L.PartialReleaseWitness leblancLayeredProfile
leblancWeakPartial = L.partial-release-witness
  refl
  (inj₂ (inj₂ (inj₁ refl)))
  "A public report exists while the underlying database status is unresolved; this is proof-search state only, not a documented private/public layer contrast."

------------------------------------------------------------------------
-- Monica Jacinto / Monica Reza alloy patent
------------------------------------------------------------------------

rezaGovernance : L.LayerReceipt
rezaGovernance = L.layer-receipt
  "Burn-resistant and high tensile strength metal alloys"
  L.governanceRestriction
  L.unknown
  "US20040208777A1 / US10/769,195"
  "The patent record establishes filing/publication and assignments, not a prior restricted technical state."

rezaReport : L.LayerReceipt
rezaReport = L.layer-receipt
  "US20040208777A1"
  L.publicTechnicalReport
  L.public
  "Google Patents / USPTO lineage for US20040208777A1"
  "The patent application publicly discloses the claimed alloy invention."

rezaData : L.LayerReceipt
rezaData = L.layer-receipt
  "Underlying alloy test data"
  L.underlyingData
  L.unknown
  "US20040208777A1 inspected public patent record"
  "The public patent does not by itself establish public release or private custody of the complete underlying test dataset."

rezaHardware : L.LayerReceipt
rezaHardware = L.layer-receipt
  "Alloy processing/manufacturing hardware"
  L.physicalHardware
  L.unknown
  "US20040208777A1"
  "No public-custody claim is made for manufacturing hardware."

rezaKnowHow : L.LayerReceipt
rezaKnowHow = L.layer-receipt
  "Manufacturing/process tacit know-how"
  L.implementationKnowHow
  L.unknown
  "US20040208777A1"
  "Patent disclosure does not establish that all tacit process knowledge was public."

rezaDerivatives : L.LayerReceipt
rezaDerivatives = L.layer-receipt
  "Later alloy/process derivatives"
  L.derivedPrivateResults
  L.unknown
  "Public patent lineage inspected to date"
  "No derivative release state is claimed."

rezaLayeredProfile : L.LayeredReleaseProfile
rezaLayeredProfile = L.layered-release-profile
  "Monica Jacinto / Monica Reza alloy patent lineage"
  rezaGovernance rezaReport rezaData rezaHardware rezaKnowHow rezaDerivatives
  "US20040208777A1 / US10/769,195"

rezaWeakPartial : L.PartialReleaseWitness rezaLayeredProfile
rezaWeakPartial = L.partial-release-witness
  refl
  (inj₂ (inj₂ (inj₁ refl)))
  "Patent is public while underlying data status is unresolved; this is not a documented bounded-underlayer witness."

------------------------------------------------------------------------
-- Anthony Chavez / DARHT-Scorpius public engineering reporting
------------------------------------------------------------------------

chavezGovernance : L.LayerReceipt
chavezGovernance = L.layer-receipt
  "DARHT / Scorpius engineering programme"
  L.governanceRestriction
  L.unknown
  "LANL National Security Science public Scorpius/DARHT reporting"
  "The public-facing articles concern a national-security programme, but this bounded fixture does not infer a formal classification/release state for the specific public article."

chavezReport : L.LayerReceipt
chavezReport = L.layer-receipt
  "DARHT / Scorpius public engineering description"
  L.publicTechnicalReport
  L.public
  "LANL National Security Science Spring/Summer 2025 issues"
  "LANL publicly explains accelerator architecture, radiographic capability and engineering roles."

chavezData : L.LayerReceipt
chavezData = L.layer-receipt
  "DARHT / Scorpius experiment data"
  L.underlyingData
  L.unknown
  "LANL public reporting inspected to date"
  "Public articles discuss the purpose and value of experimental data, but do not establish the release state of the complete experiment datasets."

chavezHardware : L.LayerReceipt
chavezHardware = L.layer-receipt
  "DARHT / Scorpius accelerator hardware"
  L.physicalHardware
  L.unknown
  "LANL public reporting inspected to date"
  "Public reporting describes hardware subsystems; public custody/access to the hardware is not established."

chavezKnowHow : L.LayerReceipt
chavezKnowHow = L.layer-receipt
  "DARHT / Scorpius implementation know-how"
  L.implementationKnowHow
  L.unknown
  "LANL public reporting inspected to date"
  "Public engineering profiles do not establish release of all implementation-specific know-how."

chavezDerivatives : L.LayerReceipt
chavezDerivatives = L.layer-receipt
  "Scorpius successor/derived engineering results"
  L.derivedPrivateResults
  L.unknown
  "LANL public reporting inspected to date"
  "No same-object derivative release status is claimed."

chavezLayeredProfile : L.LayeredReleaseProfile
chavezLayeredProfile = L.layered-release-profile
  "Anthony Chavez / DARHT-Scorpius public reporting"
  chavezGovernance chavezReport chavezData chavezHardware chavezKnowHow chavezDerivatives
  "LANL National Security Science public reporting"

chavezWeakPartial : L.PartialReleaseWitness chavezLayeredProfile
chavezWeakPartial = L.partial-release-witness
  refl
  (inj₂ (inj₂ (inj₁ refl)))
  "Public programme reporting exists while underlying-data status is unresolved; no documented layer contrast is promoted."

------------------------------------------------------------------------
-- Current cross-roster interpretation
------------------------------------------------------------------------

record CurrentLayeredCrossRosterAssessment : Set where
  constructor current-layered-cross-roster-assessment
  field
    poamsDocumentedPartialReleaseOwned : Bool
    poamsDocumentedPartialReleaseOwnedIsTrue :
      poamsDocumentedPartialReleaseOwned ≡ true
    leblancDocumentedPartialReleaseOwned : Bool
    leblancDocumentedPartialReleaseOwnedIsFalse :
      leblancDocumentedPartialReleaseOwned ≡ false
    rezaDocumentedPartialReleaseOwned : Bool
    rezaDocumentedPartialReleaseOwnedIsFalse :
      rezaDocumentedPartialReleaseOwned ≡ false
    chavezDocumentedPartialReleaseOwned : Bool
    chavezDocumentedPartialReleaseOwnedIsFalse :
      chavezDocumentedPartialReleaseOwned ≡ false
    ordinaryPublicArtifactSufficientForStrongLayeredB : Bool
    ordinaryPublicArtifactSufficientForStrongLayeredBIsFalse :
      ordinaryPublicArtifactSufficientForStrongLayeredB ≡ false
    crossRosterLayeredEnrichmentEstablished : Bool
    crossRosterLayeredEnrichmentEstablishedIsFalse :
      crossRosterLayeredEnrichmentEstablished ≡ false

canonicalCurrentLayeredCrossRosterAssessment : CurrentLayeredCrossRosterAssessment
canonicalCurrentLayeredCrossRosterAssessment = current-layered-cross-roster-assessment
  true refl
  false refl
  false refl
  false refl
  false refl
  false refl

layeredControlAcquisition : L.LayeredReleaseReverseObligation
layeredControlAcquisition = L.layered-release-reverse-obligation
  "LeBlanc / Reza / Chavez matched programme strata"
  L.dataReleaseReceipt
  "recover programme-specific receipts that explicitly establish private/bounded versus public status for underlying data, hardware, know-how or derived results; do not count unknown as private"
  "whether POAMS-style documented partial release is common practice in comparable sensitive technical programmes"
  "roster enrichment, targeting, actor identity, motive or harm without denominators and selector evidence"
