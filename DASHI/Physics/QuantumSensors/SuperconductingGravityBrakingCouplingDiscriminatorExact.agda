module DASHI.Physics.QuantumSensors.SuperconductingGravityBrakingCouplingDiscriminatorExact where

-- Provenance:
-- Li & Torr PRD43 (1991), PRB46 (1992): original coupled-potential theory.
-- Kowitt PRB49 (1994): magnitude/permeability critique.
-- Noever/Koczor/Robertson AIAA-98-3139 / NASA NTRS 19990019627:
-- rotating magnetic field, NOT equivalent mechanical disk rotation.
-- Podkletnov arXiv cond-mat/9701074: reported decelerating disk response.
-- Our named conditional scalar-screening proposal is NOT established physics.
-- SymPy inverse/energy checks: scripts/check_sc_gravity_coupling_braking.py.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
import DASHI.Physics.ExoticGravity.LiTorrCoupledPotentialModelExact as LiTorr
import DASHI.Physics.ExoticGravity.LiTorrKowittMagnitudeDisputeBidiExact as Kowitt
import DASHI.Physics.ExoticGravity.NingLiYBCORotatingFieldConstraintExact as NASA
import DASHI.Physics.ExoticGravity.SuperconductingSourceVsConstitutiveEnhancementBidiExact as Split

data SourceMotion : Set where
  mechanicallyBrakingDisk : SourceMotion
  acceleratingAppliedField : SourceMotion
  fieldDiskSlipChanging : SourceMotion

data Observable : Set where
  externalWeight : Observable
  externalInertialProbe : Observable
  magneticFlux : Observable
  pumpedElectricalOutput : Observable

data GravityModel : Set where
  standardStressEnergy : GravityModel
  conjecturalLocalScalarSource : GravityModel
  conjecturalExternalScalarTransmission : GravityModel

-- Different models do not become identical merely because both use YBCO.
data Impossible : Set where

mechanicalIsNotAppliedField :
  mechanicallyBrakingDisk ≡ acceleratingAppliedField → Impossible
mechanicalIsNotAppliedField ()

localSourceIsNotExternalTransmission :
  conjecturalLocalScalarSource ≡ conjecturalExternalScalarTransmission → Impossible
localSourceIsNotExternalTransmission ()

record BrakingExperimentReceipt : Set where
  field
    sourceMotion : SourceMotion
    output : Observable
    model : GravityModel
    timeResolvedRotationMeasured : Bool
    timeResolvedAppliedFieldMeasured : Bool
    trappedFluxMeasured : Bool
    phaseAndTemperatureMeasured : Bool
    inputPowerAndLossMeasured : Bool
    independentExternalProbeMeasured : Bool
    originalSource : String
    note : String

-- NASA's original experiment is a source-attributed null for its OWN
-- rotating-field configuration. It does not document a Podkletnov-style
-- mechanically braking high-RPM rotor with equal flux history.
nasaFieldRegime : BrakingExperimentReceipt
nasaFieldRegime = record
  { sourceMotion = acceleratingAppliedField
  ; output = externalWeight
  ; model = standardStressEnergy
  ; timeResolvedRotationMeasured = false
  ; timeResolvedAppliedFieldMeasured = false
  ; trappedFluxMeasured = false
  ; phaseAndTemperatureMeasured = false
  ; inputPowerAndLossMeasured = false
  ; independentExternalProbeMeasured = true
  ; originalSource = "NASA NTRS 19990019627 (Noever/Koczor/Robertson)"
  ; note = "Record is a source-scope witness: false means original time series not independently acquired here, not that original experimenters lacked instrumentation"
  }

-- Existing source ownership retained; no new physics credited to it.
originalLiTorr : LiTorr.LiTorrSourceRegistry
originalLiTorr = LiTorr.canonicalLiTorrSourceRegistry

originalMagnitudeCritique : Kowitt.MagnitudeDisputeReceipt
originalMagnitudeCritique = Kowitt.canonicalMagnitudeDisputeReceipt

originalNASA : NASA.RotatingFieldYBCOExperiment
originalNASA = NASA.canonicalRotatingFieldExperiment

originalSplit : Split.SourceConstitutiveBoundary
originalSplit = Split.canonicalSourceConstitutiveBoundary
