module DASHI.Physics.QuantumSensors.NVOpticalPhotonReadoutExact where

-- Finite optical contrast readout for an NV-centre spin sensor.
-- All physical contrast, preparation, collection and detector parameters
-- are explicit inputs; no observed photon statistics are fabricated.
-- Connections: prior DiamondMCG NV finite resonance / optical metrology,
-- photopharmacology, single-photon detector and causal intervention owners.

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.QuantumSensors.NVFiniteResonanceReadoutExact as NV
import DASHI.Physics.Measurement.CausalBioelectromagneticExperimentExact as Bio

record OpticalDetector : Set where
  constructor optical-detector
  field
    brightCount darkCount backgroundCount : ℚ
    microwaveReference : ℚ
open OpticalDetector public

-- The population of m_s=0 is inferred from a preparation-and-response
-- model. No positivity or upper bound is assumed automatically.
record PopulationReadout : Set where
  constructor population-readout
  field
    p0 : ℚ
    pExcited : ℚ
    normalized : p0 + pExcited ≡ 1ℚ
open PopulationReadout public

-- Bright/dark fluorescence *means*, not photon samples.
expectedCount : OpticalDetector → PopulationReadout → ℚ
expectedCount detector p =
  p0 p * brightCount detector +
  pExcited p * darkCount detector +
  backgroundCount detector

-- Both terms reduce to the same value when contrast vanishes.
zeroContrastIndependentOfPopulation :
  (p : PopulationReadout) (bright background : ℚ) →
  expectedCount (optical-detector bright bright background 1ℚ) p
  ≡ bright + background
zeroContrastIndependentOfPopulation (population-readout x y eq) bright background
  rewrite sym eq = solve (x ∷ y ∷ bright ∷ background ∷ [])
  where
    open import Relation.Binary.PropositionalEquality using (sym)

-- Optical transfer from a frequency predictor must be provided as a
-- device-specific state-preparation/readout law; an ODMR line is not
-- definitionally a detected photon count.
record OpticalNVTransfer : Set where
  constructor optical-transfer
  field
    detector : OpticalDetector
    populationFromResonance : NV.SymbolicODMRDatum → PopulationReadout
open OpticalNVTransfer public

predictPhotonMean : OpticalNVTransfer → NV.SymbolicODMRDatum → ℚ
predictPhotonMean transfer resonance =
  expectedCount (detector transfer) (populationFromResonance transfer resonance)

predictPhotonMeanRespectEquality :
  (transfer : OpticalNVTransfer) (a b : NV.SymbolicODMRDatum) →
  a ≡ b → predictPhotonMean transfer a ≡ predictPhotonMean transfer b
predictPhotonMeanRespectEquality transfer a b equality =
  cong (predictPhotonMean transfer) equality
