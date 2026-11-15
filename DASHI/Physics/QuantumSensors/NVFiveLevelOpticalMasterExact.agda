module DASHI.Physics.QuantumSensors.NVFiveLevelOpticalMasterExact where

-- Five-level NV optical cycle as a finite classical population master equation.
-- Ground g0/g1, excited e0/e1, metastable singlet shelving s.
-- Derived using the same continuous-time jump/master-generator pattern as
-- DASHI.Biology.Physical.FiniteChemicalMasterGeneratorExact (Gillespie 1977).
-- This is a phenomenological reduction of the NV optical cycle, not a
-- Lindblad derivation or a calibrated seven-level nitrogen-vacancy model.
-- Nonnegative rate assumptions and optical collection calibration are
-- mandatory for physical probabilistic interpretation.

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

record Rates : Set where
  constructor rates
  field
    pump microwave : ℚ
    fluorescence0 fluorescence1 : ℚ
    isc0 isc1 : ℚ
    shelfTo0 shelfTo1 : ℚ
open Rates public

record Populations : Set where
  constructor populations
  field
    g0 g1 e0 e1 s : ℚ
open Populations public

totalMass : Populations → ℚ
totalMass p = g0 p + g1 p + e0 p + e1 p + s p

-- Each edge appears as an equal and opposite source/sink.
-- Laser pumping g_i -> e_i; radiative return e_i -> g_i;
-- ISC e_i -> s; singlet decay s -> g_i; microwave exchange g0 <-> g1.
derivative : Rates → Populations → Populations
derivative r p = populations
  ((fluorescence0 r * e0 p + shelfTo0 r * s p + microwave r * g1 p)
    - (pump r * g0 p + microwave r * g0 p))
  ((fluorescence1 r * e1 p + shelfTo1 r * s p + microwave r * g0 p)
    - (pump r * g1 p + microwave r * g1 p))
  (pump r * g0 p - (fluorescence0 r * e0 p + isc0 r * e0 p))
  (pump r * g1 p - (fluorescence1 r * e1 p + isc1 r * e1 p))
  (isc0 r * e0 p + isc1 r * e1 p
    - (shelfTo0 r * s p + shelfTo1 r * s p))

totalDerivative : Rates → Populations → ℚ
totalDerivative r p = totalMass (derivative r p)

massConservedInfinitesimally :
  (r : Rates) (p : Populations) → totalDerivative r p ≡ 0ℚ
massConservedInfinitesimally r p = solve-∀

record PhotonCollection : Set where
  constructor collection
  field
    detectionGain0 detectionGain1 background : ℚ
open PhotonCollection public

expectedPhotonRate : PhotonCollection → Rates → Populations → ℚ
expectedPhotonRate d r p =
  detectionGain0 d * fluorescence0 r * e0 p
  + detectionGain1 d * fluorescence1 r * e1 p
  + background d

-- A zero fluorescence detection gain leaves only background.
zeroGainGivesBackground :
  (r : Rates) (p : Populations) (background : ℚ) →
  expectedPhotonRate (collection 0ℚ 0ℚ background) r p ≡ background
zeroGainGivesBackground r p background = solve-∀

-- Unlike the previous 2-level steady-state surrogate, this includes
-- excited populations and singlet shelving, enabling explicit ISC
-- hypotheses; positivity, steady state, and measured rates remain open.
