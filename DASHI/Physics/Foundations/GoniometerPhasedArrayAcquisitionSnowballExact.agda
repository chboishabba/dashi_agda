module DASHI.Physics.Foundations.GoniometerPhasedArrayAcquisitionSnowballExact where

open import DASHI.Core.Prelude

import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Core.SnowballPluralLensDiscoveryAdmissionExact as Discovery
import DASHI.Physics.Foundations.PhasedArrayRFSensingSourceAtlasExact as Sources
import DASHI.Physics.Foundations.InterferometricDirectionFindingSourceAtlasExact as InterferometricSources
import DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingExact as Goniometer
import DASHI.Physics.Foundations.PhasedArrayDirectionFindingExact as Array

------------------------------------------------------------------------
-- ACQUISITION SNOWBALL
--
-- Sources pay only the bounded historical/technical leaves named below.
-- Repository synthesis relates those leaves to the existing goniometer and
-- phased-array observer roles.  No acquired source identifies the user's
-- observed instrument, exact unit, mission, emitter, or operational authority.
------------------------------------------------------------------------

record HistoricalGoniometerAcquisition : Set where
  constructor historical-goniometer-acquisition
  field
    patentSourceRetained :
      Snowball.SourceRoleSnowballReceipt Sources.belliniTosiPatentPrimary
    contemporaryHistoricalSourceRetained :
      Snowball.SourceRoleSnowballReceipt Sources.belliniTosiNatureHistorical
    archivalObjectSourceRetained :
      Snowball.SourceRoleSnowballReceipt Sources.belliniTosiOxfordArchive
    mechanismSourceRetained :
      Snowball.SourceRoleSnowballReceipt Sources.belliniTosiMuseumMechanism
    directedWirelessLineagePaid : Bool
    directedWirelessLineagePaidIsTrue : directedWirelessLineagePaid ≡ true
    rotatableSearchCoilMechanismPaid : Bool
    rotatableSearchCoilMechanismPaidIsTrue :
      rotatableSearchCoilMechanismPaid ≡ true
    belliniTosiWasReceptionDFSystemPaid : Bool
    belliniTosiWasReceptionDFSystemPaidIsTrue :
      belliniTosiWasReceptionDFSystemPaid ≡ true
    observedInstrumentSameObjectPaid : Bool
    observedInstrumentSameObjectPaidIsFalse :
      observedInstrumentSameObjectPaid ≡ false
open HistoricalGoniometerAcquisition public

canonicalHistoricalGoniometerAcquisition : HistoricalGoniometerAcquisition
canonicalHistoricalGoniometerAcquisition =
  historical-goniometer-acquisition
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.belliniTosiPatentPrimary)
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.belliniTosiNatureHistorical)
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.belliniTosiOxfordArchive)
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.belliniTosiMuseumMechanism)
    true refl
    true refl
    true refl
    false refl

record PhasedArrayAngleAcquisition : Set where
  constructor phased-array-angle-acquisition
  field
    monopulsePrimaryRetained :
      Snowball.SourceRoleSnowballReceipt Sources.phasedArrayMonopulsePrimary
    governmentAngleReportRetained :
      Snowball.SourceRoleSnowballReceipt Sources.phasedArrayGovernmentAngleReport
    phasedArrayMonopulseAngleRelationshipPaid : Bool
    phasedArrayMonopulseAngleRelationshipPaidIsTrue :
      phasedArrayMonopulseAngleRelationshipPaid ≡ true
    sumDifferenceAngularObservationPaid : Bool
    sumDifferenceAngularObservationPaidIsTrue :
      sumDifferenceAngularObservationPaid ≡ true
    everyPhasedArrayUsesMonopulsePaid : Bool
    everyPhasedArrayUsesMonopulsePaidIsFalse :
      everyPhasedArrayUsesMonopulsePaid ≡ false
    phasedArrayAngleDeterminesExactWorldPaid : Bool
    phasedArrayAngleDeterminesExactWorldPaidIsFalse :
      phasedArrayAngleDeterminesExactWorldPaid ≡ false
open PhasedArrayAngleAcquisition public

canonicalPhasedArrayAngleAcquisition : PhasedArrayAngleAcquisition
canonicalPhasedArrayAngleAcquisition =
  phased-array-angle-acquisition
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.phasedArrayMonopulsePrimary)
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.phasedArrayGovernmentAngleReport)
    true refl
    true refl
    false refl
    false refl

record InterferometricDFAcquisition : Set where
  constructor interferometric-df-acquisition
  field
    phaseDifferenceAoASourceRetained :
      Snowball.SourceRoleSnowballReceipt InterferometricSources.phaseDifferenceAoAPrimary
    correlativeInterferometerSourceRetained :
      Snowball.SourceRoleSnowballReceipt InterferometricSources.correlativeInterferometerDFPrimary
    phaseDifferenceToAoARelationshipPaid : Bool
    phaseDifferenceToAoARelationshipPaidIsTrue :
      phaseDifferenceToAoARelationshipPaid ≡ true
    antennaArrayPhaseDFRelationshipPaid : Bool
    antennaArrayPhaseDFRelationshipPaidIsTrue :
      antennaArrayPhaseDFRelationshipPaid ≡ true
    phaseObservationIsUnambiguousForAllGeometryPaid : Bool
    phaseObservationIsUnambiguousForAllGeometryPaidIsFalse :
      phaseObservationIsUnambiguousForAllGeometryPaid ≡ false
open InterferometricDFAcquisition public

canonicalInterferometricDFAcquisition : InterferometricDFAcquisition
canonicalInterferometricDFAcquisition =
  interferometric-df-acquisition
    (Snowball.canonicalSourceRoleSnowballReceipt InterferometricSources.phaseDifferenceAoAPrimary)
    (Snowball.canonicalSourceRoleSnowballReceipt InterferometricSources.correlativeInterferometerDFPrimary)
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- Acquisition frontier.  Paid leaves are distinct from remaining source debt.
------------------------------------------------------------------------

data AcquisitionLeaf : Set where
  belliniTosiPatentLeaf : AcquisitionLeaf
  belliniTosiMechanismLeaf : AcquisitionLeaf
  historicalReceptionDFLeaf : AcquisitionLeaf
  exactObservedInstrumentLeaf : AcquisitionLeaf
  phasedArrayMonopulseLeaf : AcquisitionLeaf
  sumDifferenceAngleLeaf : AcquisitionLeaf
  phaseComparisonInterferometerPrimaryLeaf : AcquisitionLeaf
  exactOperationalUseLeaf : AcquisitionLeaf

data LeafStatus : Set where
  paid : LeafStatus
  unpaid : LeafStatus
  boundedUnresolved : LeafStatus

acquisitionStatus : AcquisitionLeaf → LeafStatus
acquisitionStatus belliniTosiPatentLeaf = paid
acquisitionStatus belliniTosiMechanismLeaf = paid
acquisitionStatus historicalReceptionDFLeaf = paid
acquisitionStatus exactObservedInstrumentLeaf = boundedUnresolved
acquisitionStatus phasedArrayMonopulseLeaf = paid
acquisitionStatus sumDifferenceAngleLeaf = paid
acquisitionStatus phaseComparisonInterferometerPrimaryLeaf = paid
acquisitionStatus exactOperationalUseLeaf = boundedUnresolved

record AcquisitionFrontier : Set where
  constructor acquisition-frontier
  field
    historicalPatentPaid : acquisitionStatus belliniTosiPatentLeaf ≡ paid
    historicalMechanismPaid : acquisitionStatus belliniTosiMechanismLeaf ≡ paid
    receptionDFHistoryPaid : acquisitionStatus historicalReceptionDFLeaf ≡ paid
    exactObservedInstrumentStillUnresolved :
      acquisitionStatus exactObservedInstrumentLeaf ≡ boundedUnresolved
    phasedArrayMonopulsePaid : acquisitionStatus phasedArrayMonopulseLeaf ≡ paid
    sumDifferenceAnglePaid : acquisitionStatus sumDifferenceAngleLeaf ≡ paid
    phaseComparisonPrimaryPaid :
      acquisitionStatus phaseComparisonInterferometerPrimaryLeaf ≡ paid
    operationalUseStillUnresolved :
      acquisitionStatus exactOperationalUseLeaf ≡ boundedUnresolved
open AcquisitionFrontier public

canonicalAcquisitionFrontier : AcquisitionFrontier
canonicalAcquisitionFrontier =
  acquisition-frontier refl refl refl refl refl refl refl refl

------------------------------------------------------------------------
-- Existing formal endpoints remain explicit after acquisition.
------------------------------------------------------------------------

mechanicalGoniometerStillCarriesAngleRole :
  Goniometer.implementationRole Goniometer.mechanicalAngleReadout
  ≡ Goniometer.angleEstimationRole
mechanicalGoniometerStillCarriesAngleRole = refl

phaseComparisonStillCarriesAngleRole :
  Goniometer.implementationRole Goniometer.phaseComparison
  ≡ Goniometer.angleEstimationRole
phaseComparisonStillCarriesAngleRole = refl

phasedArrayStillCarriesAngularRole :
  Array.supportsAngularObservation Array.electronicallySteeredPhasedArray
  ≡ Array.angularObservationRole
phasedArrayStillCarriesAngularRole = refl

phaseComparisonArrayStillCarriesAngularRole :
  Array.supportsAngularObservation Array.phaseComparisonInterferometer
  ≡ Array.angularObservationRole
phaseComparisonArrayStillCarriesAngularRole = refl

arrayBearingStillCoarse : ¬ Array.ArrayBearingDeterminesExactEmitterWorld
arrayBearingStillCoarse = Array.arrayBearingDoesNotDetermineExactEmitterWorld

goniometerBearingStillCoarse : ¬ Goniometer.BearingDeterminesExactEmitterWorld
goniometerBearingStillCoarse = Goniometer.bearingDoesNotDetermineExactEmitterWorld

------------------------------------------------------------------------
-- The previously unpaid phase-comparison leaf is now paid by primary sources.
-- Discovery remains recorded as the reason the acquisition happened; payment
-- does not erase the proof-search/snowball history.
------------------------------------------------------------------------

data AcquisitionAxis : Set where
  primaryInterferometricDFSourceAxis : AcquisitionAxis

phaseComparisonPrimaryAcquisitionTrace : Discovery.AxisProposal AcquisitionAxis
phaseComparisonPrimaryAcquisitionTrace = Discovery.axis-proposal
  primaryInterferometricDFSourceAxis
  Discovery.sourceProvenanceMismatch
  "phase-comparison/interferometric direction-finding consumer"
  "which primary source pays phase-difference/array-baseline to direction-of-arrival inference?"
  "failed acquisition frontier exposed a source-payment gap; Younger 2017 and Oh et al. 2023 now pay the bounded leaf"
  "community/forum terminology did not pay this leaf"
  "source acquisition does not identify exact observed hardware or create operational authority"

record AcquisitionAuthorityFirewall : Set where
  constructor acquisition-authority-firewall
  field
    patentCitationImportsProof : Bool
    patentCitationImportsProofIsFalse : patentCitationImportsProof ≡ false
    archivalSimilarityIdentifiesObservedInstrument : Bool
    archivalSimilarityIdentifiesObservedInstrumentIsFalse :
      archivalSimilarityIdentifiesObservedInstrument ≡ false
    primaryTechnicalSourceDeterminesExactHardware : Bool
    primaryTechnicalSourceDeterminesExactHardwareIsFalse :
      primaryTechnicalSourceDeterminesExactHardware ≡ false
    communityLeadMayPayPrimaryLeaf : Bool
    communityLeadMayPayPrimaryLeafIsFalse :
      communityLeadMayPayPrimaryLeaf ≡ false
    acquiredCapabilityCreatesOperationalAuthority : Bool
    acquiredCapabilityCreatesOperationalAuthorityIsFalse :
      acquiredCapabilityCreatesOperationalAuthority ≡ false
open AcquisitionAuthorityFirewall public

canonicalAcquisitionAuthorityFirewall : AcquisitionAuthorityFirewall
canonicalAcquisitionAuthorityFirewall =
  acquisition-authority-firewall
    false refl
    false refl
    false refl
    false refl
    false refl
