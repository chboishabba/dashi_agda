module DASHI.Physics.Foundations.CabarlahGoniometerAcquisitionExact where

open import DASHI.Core.Prelude

import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Physics.Foundations.CabarlahDirectionFindingSourceAtlasExact as Sources
import DASHI.Physics.Foundations.CabarlahSignalInferenceExact as Cabarlah
import DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingExact as Goniometer
import DASHI.Physics.Foundations.PhasedArrayDirectionFindingExact as Array

------------------------------------------------------------------------
-- CABARLAH DIRECTION-FINDING ACQUISITION
--
-- The acquired record is now strong enough to pay a Cabarlah DF lineage:
-- Army SIGINT base, first-person medium-range DF testimony, and later CDAA
-- HF-DF installations.  It is not strong enough to identify a Bellini-Tosi
-- goniometer at Cabarlah or to prove the user's observed instrument came from
-- Cabarlah.  Those remain explicit same-object/provenance debts.
------------------------------------------------------------------------

record CabarlahDirectionFindingAcquisition : Set where
  constructor cabarlah-direction-finding-acquisition
  field
    armyHistoryRetained :
      Snowball.SourceRoleSnowballReceipt Sources.armyResearchCabarlahSIGINT
    oralHistoryRetained :
      Snowball.SourceRoleSnowballReceipt Sources.cabarlahMediumRangeDFOralHistory
    cdaaHistoryRetained :
      Snowball.SourceRoleSnowballReceipt Sources.anuCabarlahCDAAHistory
    raafHFDFSourceRetained :
      Snowball.SourceRoleSnowballReceipt Sources.raafCabarlahHFDFConference

    cabarlahArmySIGINTLineagePaid : Bool
    cabarlahArmySIGINTLineagePaidIsTrue :
      cabarlahArmySIGINTLineagePaid ≡ true

    cabarlahDirectionFindingCapabilityPaid : Bool
    cabarlahDirectionFindingCapabilityPaidIsTrue :
      cabarlahDirectionFindingCapabilityPaid ≡ true

    cabarlahMediumRangeDFInstallationPaid : Bool
    cabarlahMediumRangeDFInstallationPaidIsTrue :
      cabarlahMediumRangeDFInstallationPaid ≡ true

    cabarlahCDAAHFDFPaid : Bool
    cabarlahCDAAHFDFPaidIsTrue :
      cabarlahCDAAHFDFPaid ≡ true

open CabarlahDirectionFindingAcquisition public

canonicalCabarlahDirectionFindingAcquisition :
  CabarlahDirectionFindingAcquisition
canonicalCabarlahDirectionFindingAcquisition =
  cabarlah-direction-finding-acquisition
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.armyResearchCabarlahSIGINT)
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.cabarlahMediumRangeDFOralHistory)
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.anuCabarlahCDAAHistory)
    (Snowball.canonicalSourceRoleSnowballReceipt Sources.raafCabarlahHFDFConference)
    true refl
    true refl
    true refl
    true refl

------------------------------------------------------------------------
-- What the acquisition still does NOT pay.
------------------------------------------------------------------------

record CabarlahGoniometerBoundary : Set where
  constructor cabarlah-goniometer-boundary
  field
    cabarlahUsedDirectionFinding : Bool
    cabarlahUsedDirectionFindingIsTrue :
      cabarlahUsedDirectionFinding ≡ true

    cabarlahUsedBelliniTosiGoniometerPaid : Bool
    cabarlahUsedBelliniTosiGoniometerPaidIsFalse :
      cabarlahUsedBelliniTosiGoniometerPaid ≡ false

    observedInstrumentCameFromCabarlahPaid : Bool
    observedInstrumentCameFromCabarlahPaidIsFalse :
      observedInstrumentCameFromCabarlahPaid ≡ false

    observedInstrumentExactModelPaid : Bool
    observedInstrumentExactModelPaidIsFalse :
      observedInstrumentExactModelPaid ≡ false

    contextualCabarlahRDFProvenanceHypothesis : Bool
    contextualCabarlahRDFProvenanceHypothesisIsTrue :
      contextualCabarlahRDFProvenanceHypothesis ≡ true

    contextualHypothesisEqualsSameObjectProof : Bool
    contextualHypothesisEqualsSameObjectProofIsFalse :
      contextualHypothesisEqualsSameObjectProof ≡ false

open CabarlahGoniometerBoundary public

canonicalCabarlahGoniometerBoundary : CabarlahGoniometerBoundary
canonicalCabarlahGoniometerBoundary =
  cabarlah-goniometer-boundary
    true refl
    false refl
    false refl
    false refl
    true refl
    false refl

------------------------------------------------------------------------
-- Cross-pollination with the pre-existing repo owners.
--
-- Cabarlah's historical CDAA/HF-DF lineage is an array-based direction-finding
-- lineage, but it is not thereby an electronically steered phased-array radar.
-- Likewise, the mechanical goniometer and later array systems can share the
-- abstract angular-observation role without hardware identity.
------------------------------------------------------------------------

record CabarlahObserverCrossPollination : Set where
  constructor cabarlah-observer-cross-pollination
  field
    cabarlahSignalInferenceStillNonInjective :
      ¬ Cabarlah.SignalInferenceInjective

    mechanicalGoniometerCarriesAngleRole :
      Goniometer.implementationRole Goniometer.mechanicalAngleReadout
      ≡ Goniometer.angleEstimationRole

    phasedArrayCarriesAngularRole :
      Array.supportsAngularObservation Array.electronicallySteeredPhasedArray
      ≡ Array.angularObservationRole

    cabarlahCDAAEqualsElectronicPhasedArrayRadar : Bool
    cabarlahCDAAEqualsElectronicPhasedArrayRadarIsFalse :
      cabarlahCDAAEqualsElectronicPhasedArrayRadar ≡ false

    commonAngularRoleImpliesSameHardware : Bool
    commonAngularRoleImpliesSameHardwareIsFalse :
      commonAngularRoleImpliesSameHardware ≡ false

    directionFindingDeterminesExactWorld : Bool
    directionFindingDeterminesExactWorldIsFalse :
      directionFindingDeterminesExactWorld ≡ false

    cabarlahCapabilityCreatesOperationalAuthority : Bool
    cabarlahCapabilityCreatesOperationalAuthorityIsFalse :
      cabarlahCapabilityCreatesOperationalAuthority ≡ false

open CabarlahObserverCrossPollination public

canonicalCabarlahObserverCrossPollination : CabarlahObserverCrossPollination
canonicalCabarlahObserverCrossPollination =
  cabarlah-observer-cross-pollination
    Cabarlah.signalInferenceIsNotInjective
    refl
    refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Acquisition frontier: the direct Cabarlah-to-goniometer object link remains
-- the live debt exposed by the search rather than being inferred from role
-- compatibility or from the existence of DF installations at the base.
------------------------------------------------------------------------

data CabarlahAcquisitionLeaf : Set where
  armySIGINTBaseLeaf : CabarlahAcquisitionLeaf
  mediumRangeDFAtCabarlahLeaf : CabarlahAcquisitionLeaf
  cdaaHFDFAtCabarlahLeaf : CabarlahAcquisitionLeaf
  belliniTosiAtCabarlahLeaf : CabarlahAcquisitionLeaf
  observedGoniometerCabarlahSameObjectLeaf : CabarlahAcquisitionLeaf

data CabarlahLeafStatus : Set where
  paid : CabarlahLeafStatus
  unpaid : CabarlahLeafStatus
  boundedUnresolved : CabarlahLeafStatus

cabarlahAcquisitionStatus : CabarlahAcquisitionLeaf → CabarlahLeafStatus
cabarlahAcquisitionStatus armySIGINTBaseLeaf = paid
cabarlahAcquisitionStatus mediumRangeDFAtCabarlahLeaf = paid
cabarlahAcquisitionStatus cdaaHFDFAtCabarlahLeaf = paid
cabarlahAcquisitionStatus belliniTosiAtCabarlahLeaf = unpaid
cabarlahAcquisitionStatus observedGoniometerCabarlahSameObjectLeaf = boundedUnresolved

record CabarlahAcquisitionFrontier : Set where
  constructor cabarlah-acquisition-frontier
  field
    armySIGINTPaid : cabarlahAcquisitionStatus armySIGINTBaseLeaf ≡ paid
    mediumRangeDFPaid : cabarlahAcquisitionStatus mediumRangeDFAtCabarlahLeaf ≡ paid
    cdaaHFDFPaid : cabarlahAcquisitionStatus cdaaHFDFAtCabarlahLeaf ≡ paid
    belliniTosiAtCabarlahStillUnpaid :
      cabarlahAcquisitionStatus belliniTosiAtCabarlahLeaf ≡ unpaid
    observedGoniometerCabarlahStillUnresolved :
      cabarlahAcquisitionStatus observedGoniometerCabarlahSameObjectLeaf
      ≡ boundedUnresolved
open CabarlahAcquisitionFrontier public

canonicalCabarlahAcquisitionFrontier : CabarlahAcquisitionFrontier
canonicalCabarlahAcquisitionFrontier =
  cabarlah-acquisition-frontier refl refl refl refl refl
