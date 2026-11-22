module DASHI.Physics.Motors.SmithFilsingerSwitchedCoupledStorageBidiExact where

-- Source-grounded conditional S1/S3 nonlinear steelman of the earlier
-- user-transcribed Filsinger NST midpoint/cap/coil/diode/spark mechanism,
-- with the separate historical Smith/Kelly magnetic coupling as PRIOR ART.
-- NO original photographed pin-level reconstruction is claimed.
-- Reuse the existing finite charge/time/energy and same-object owners.
--
-- The local analytic companion derives the physical differential identities
-- in SymPy, and integrates piecewise switching numerically. The Agda
-- content here is a *typed finite work contract*, NOT a symbolic ODE proof.
--
-- scripts: /mnt/data/check_smith_filsinger_switched_s1_s3_bidi_20261122.py
-- Agda kernel acceptance not attempted; no GH CI.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)

import DASHI.Physics.Motors.SmithFilsingerTimeIndexedTransferExact as Timed
import DASHI.Physics.Motors.SmithFilsingerSourceEdgeAdmissionBidiExact as Speech
import DASHI.Physics.Motors.SmithFilsingerWindingOwnerReturnCutBidiExact as Return
import DASHI.Physics.Motors.Circuit36927ComponentGraphExact as Pins
import DASHI.Physics.Foundations.SameObjectConservationLedgerExact as SourceLedger
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

data ConditionalCircuit : Set where
  S1CentreReferencedDiodeOr : ConditionalCircuit
  S3MagneticallyCoupledDisplacementReturn : ConditionalCircuit

data SwitchPosition : Set where
  sparkOff sparkOn : SwitchPosition

data DonorHypothesis : Set where
  driverOnly explicitExternalPort : DonorHypothesis

-- These are two different source-worlds despite identical original speech.
data SpokenObservation : Set where
  sameFourMidpointPhrases : SpokenObservation

spoken : ConditionalCircuit → SpokenObservation
spoken S1CentreReferencedDiodeOr = sameFourMidpointPhrases
spoken S3MagneticallyCoupledDisplacementReturn = sameFourMidpointPhrases

distinctCircuit :
  S1CentreReferencedDiodeOr
    ≡ S3MagneticallyCoupledDisplacementReturn → ⊥
distinctCircuit ()

-- Both theories may produce the same source-text signature. Unlike a
-- physical pin/electrical observation, this is not an inverse witness.
noUniqueOriginalCircuitFromSpeech :
  (decode : SpokenObservation → ConditionalCircuit) →
  ((c : ConditionalCircuit) → decode (spoken c) ≡ c) → ⊥
noUniqueOriginalCircuitFromSpeech decode agree =
  distinctCircuit (transitional (agree S1CentreReferencedDiodeOr)
                                (agree S3MagneticallyCoupledDisplacementReturn))
  where
    transitional :
      {x y z : ConditionalCircuit} →
      z ≡ x → z ≡ y → x ≡ y
    transitional refl refl = refl

-- Constitutive/model-law assumptions are separate from physical evidence.
-- The chosen nonlinear piecewise operator has an ordinary nonnegative
-- diode forward drop and series resistance, a reservoir capacitor and a
-- hysteretic spark conductance. It is not claimed as the original netlist.
record CandidateOperator : Set₁ where
  field
    selectedCircuit : ConditionalCircuit
    sameSpeech : spoken selectedCircuit ≡ sameFourMidpointPhrases
    originalPinReference : Pins.SourceBoundCircuit
    SourceLaw : Set
    signedDiodeAndSparkConstitutiveLaw : SourceLaw
    storageStateResetWitness : Set
    sourceSpecificReset : storageStateResetWitness

-- Reuse the existing source-separated bounded interval, rather than
-- treating capacitor VAR, spark pulse or ground label as free source work.
record SwitchedPaidInterval : Set where
  constructor switched-paid-interval
  field
    selected : ConditionalCircuit
    hypothesis : DonorHypothesis
    sparkBefore : SwitchPosition
    sparkAfter : SwitchPosition
    window : Timed.BoundedWorkWindow
    sourceSignedEarthPortAdmitted : Set
    sourceWorkWitness : sourceSignedEarthPortAdmitted

loadBound : (r : SwitchedPaidInterval) →
  Bound._≤_
    (Timed.BoundedWorkWindow.usefulOutput
      (SwitchedPaidInterval.window r))
    (Timed.allAvailable (SwitchedPaidInterval.window r))
loadBound r =
  Timed.usefulNoGreaterThanAllSources
    (SwitchedPaidInterval.window r)

-- When the model explicitly declares NO external donor, that donor work
-- must be zero. Its presence is not deduced from earth-ground vocabulary.
record DriveOnlyWindow : Set where
  constructor drive-only-window
  field
    paid : SwitchedPaidInterval
    driverOnlySelected :
      SwitchedPaidInterval.hypothesis paid ≡ driverOnly
    noExternalSource :
      Timed.BoundedWorkWindow.naturalSourceInput
        (SwitchedPaidInterval.window paid) ≡ 0

-- Genuine original-world promotion consumes the existing source proof:
-- same reel, same physical pin identities, plus source measured receipt.
record PhysicalPromotionRequired : Set₁ where
  field
    sourceEvidence : Speech.AdmissionWitness
    originalPhysicalOriginal :
      Timed.SameObjectPhysicalWeld
    SourceEnergyAndDischarge : Set
    sameOriginalMeasuredEnergy : SourceEnergyAndDischarge

-- No PhysicalPromotionRequired is constructed and no Agda proof of a
-- real-world nonlinear Maxwell/plasma device follows from source phrases.
