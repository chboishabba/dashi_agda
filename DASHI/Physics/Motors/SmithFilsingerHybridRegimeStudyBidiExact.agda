module DASHI.Physics.Motors.SmithFilsingerHybridRegimeStudyBidiExact where

-- Distinct original sources/papers/patents and finite causal event semantics.
-- This file does NOT promote experimental study findings into Agda theorems.
-- Physical same-object admission and Agda kernel checking remain open.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
import DASHI.Physics.Motors.SmithFilsingerTimeIndexedTransferExact as Time
import DASHI.Physics.Motors.Circuit36927SwitchStateExact as Switch
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound
import DASHI.Promotion.MaxwellExteriorCalculusAdapter as Maxwell

data Empty : Set where

data Study : Set where
  golkowski2010 cohen2010 cohen2011 papadopoulos2011 icd2011 : Study
  fosterFinch1974 kimMetamaterial2026 kimZhongJing2026 : Study
  ultrasoundCarrierSidebandPatent ultrasoundVirtualSourcePatent : Study
  ultrasoundFocalPatent microwaveAuditoryPatent : Study
  teslaNaturalMedium hingsTelluric plausonAtmosphere : Study
  earthEnergies675 earthEnergies676 ionPowerPatent : Study
  smithMexicanApplication filsingerCommercial filsingerShunt filsingerEarth : Study

data EvidenceTier : Set where
  peerReviewedExperiment theoryAndSimulation patentClaim historicalClaim
    recordedDemonstration : EvidenceTier

evidenceTier : Study → EvidenceTier
evidenceTier golkowski2010 = peerReviewedExperiment
evidenceTier cohen2010 = peerReviewedExperiment
evidenceTier cohen2011 = theoryAndSimulation
evidenceTier papadopoulos2011 = theoryAndSimulation
evidenceTier icd2011 = peerReviewedExperiment
evidenceTier fosterFinch1974 = peerReviewedExperiment
evidenceTier kimMetamaterial2026 = peerReviewedExperiment
evidenceTier kimZhongJing2026 = peerReviewedExperiment
evidenceTier ultrasoundCarrierSidebandPatent = patentClaim
evidenceTier ultrasoundVirtualSourcePatent = patentClaim
evidenceTier ultrasoundFocalPatent = patentClaim
evidenceTier microwaveAuditoryPatent = patentClaim
evidenceTier teslaNaturalMedium = historicalClaim
evidenceTier hingsTelluric = historicalClaim
evidenceTier plausonAtmosphere = historicalClaim
evidenceTier earthEnergies675 = patentClaim
evidenceTier earthEnergies676 = patentClaim
evidenceTier ionPowerPatent = patentClaim
evidenceTier smithMexicanApplication = historicalClaim
evidenceTier filsingerCommercial = recordedDemonstration
evidenceTier filsingerShunt = recordedDemonstration
evidenceTier filsingerEarth = recordedDemonstration

data PhysicalDomain : Set where
  atmosphericAir materialThermoelastic resonantElectromechanical
    magnetosphere ionosphere originalFilsingerCircuit : PhysicalDomain

studyDomain : Study → PhysicalDomain
studyDomain golkowski2010 = magnetosphere
studyDomain cohen2010 = ionosphere
studyDomain cohen2011 = ionosphere
studyDomain papadopoulos2011 = ionosphere
studyDomain icd2011 = ionosphere
studyDomain fosterFinch1974 = materialThermoelastic
studyDomain kimMetamaterial2026 = atmosphericAir
studyDomain kimZhongJing2026 = atmosphericAir
studyDomain ultrasoundCarrierSidebandPatent = atmosphericAir
studyDomain ultrasoundVirtualSourcePatent = atmosphericAir
studyDomain ultrasoundFocalPatent = atmosphericAir
studyDomain microwaveAuditoryPatent = materialThermoelastic
studyDomain teslaNaturalMedium = ionosphere
studyDomain hingsTelluric = ionosphere
studyDomain plausonAtmosphere = atmosphericAir
studyDomain earthEnergies675 = originalFilsingerCircuit
studyDomain earthEnergies676 = originalFilsingerCircuit
studyDomain ionPowerPatent = atmosphericAir
studyDomain smithMexicanApplication = originalFilsingerCircuit
studyDomain filsingerCommercial = originalFilsingerCircuit
studyDomain filsingerShunt = originalFilsingerCircuit
studyDomain filsingerEarth = originalFilsingerCircuit

patentNotExperimental : patentClaim ≡ peerReviewedExperiment → Empty
patentNotExperimental ()

data Sensor : Set where
  microphone electricalVoltage electricalCurrent environmentalField : Sensor

microphoneNotCurrent : microphone ≡ electricalCurrent → Empty
microphoneNotCurrent ()

data HybridRegime : Set where
  pumpNotStarted startupTransient drivenHunting postPumpResidual : HybridRegime

data HybridEvent : Set where
  switchOn settle switchOff hold : HybridEvent

next : HybridEvent → HybridRegime → HybridRegime
next switchOn state = startupTransient
next settle state = drivenHunting
next switchOff state = postPumpResidual
next hold state = state

switchOffSelectsResidual : (state : HybridRegime) →
  next switchOff state ≡ postPumpResidual
switchOffSelectsResidual state = refl

holdPreservesState : (state : HybridRegime) → next hold state ≡ state
holdPreservesState state = refl

postPumpNotDriven : postPumpResidual ≡ drivenHunting → Empty
postPumpNotDriven ()

twoStageIonosphericFlight :
  (start firstDelay secondDelay : Nat) → Time.RetardedFlight
twoStageIonosphericFlight = Time.twoHopSecondFlight

twoStageArrivalLaw : (t d1 d2 : Nat) →
  Time.RetardedFlight.arrival (twoStageIonosphericFlight t d1 d2)
  ≡ (t + d1) + d2
twoStageArrivalLaw t d1 d2 = refl

record SameApparatusStudyAdmission (s : Study) : Set₁ where
  field
    SelectedStudyClaimAndEvidence : Set
    OriginalFilsingerCircuitPins : Set
    ConstitutiveLawAtActualMaterial : Set
    CausalPropagationKernel : Set
    CalibratedMicrophoneToElectricalTransfer : Set
    SignedEnvironmentalSourceWork : Set
    sourceEvidence : SelectedStudyClaimAndEvidence
    selectedPins : OriginalFilsingerCircuitPins
    materialEvidence : ConstitutiveLawAtActualMaterial
    retardedKernelEvidence : CausalPropagationKernel
    electricalObservationEvidence : CalibratedMicrophoneToElectricalTransfer
    signedWorkEvidence : SignedEnvironmentalSourceWork

-- No literature citation alone constructs a SameApparatusStudyAdmission.
