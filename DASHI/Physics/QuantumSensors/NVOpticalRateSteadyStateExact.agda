module DASHI.Physics.QuantumSensors.NVOpticalRateSteadyStateExact where

-- Minimal driven two-population NV rate model, rational steady-state balance.
-- Optical pumping rate r transfers dark -> bright; microwave-induced
-- transitions W transfer population both directions. This is a
-- phenomenological *two-level reduction* of the spin-one optical cycle,
-- not a derived NV seven-level Lindblad or intersystem crossing model.
-- All rates and fluorescence intensities need physical calibration.

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Physics.QuantumSensors.NVOpticalPhotonReadoutExact as Optical

record TwoPopulationRates : Set where
  constructor two-population-rates
  field
    pumping microwave : ℚ
    inverseTotalRate : ℚ
    inverseWitness : (pumping + microwave + microwave) * inverseTotalRate ≡ 1ℚ
open TwoPopulationRates public

-- Steady state of dp0/dt = r*(1-p0) + W*(1-2*p0).
brightPopulation : TwoPopulationRates → ℚ
brightPopulation r =
  (pumping r + microwave r) * inverseTotalRate r

darkPopulation : TwoPopulationRates → ℚ
darkPopulation r = microwave r * inverseTotalRate r

populationNormalization :
  (r : TwoPopulationRates) →
  brightPopulation r + darkPopulation r ≡ 1ℚ
populationNormalization (two-population-rates p w inv witness) =
  trans (solve (p ∷ w ∷ inv ∷ [])) witness
  where
    open import Relation.Binary.PropositionalEquality using (trans)

steadyBalance :
  (r : TwoPopulationRates) →
  pumping r * darkPopulation r ≡
  microwave r * (brightPopulation r - darkPopulation r)
steadyBalance (two-population-rates p w inv witness) =
  solve (p ∷ w ∷ inv ∷ [])

opticalPopulation : TwoPopulationRates → Optical.PopulationReadout
opticalPopulation r =
  Optical.population-readout
    (brightPopulation r) (darkPopulation r)
    (populationNormalization r)

predictedRatePhotonMean :
  Optical.OpticalDetector → TwoPopulationRates → ℚ
predictedRatePhotonMean detector r =
  Optical.expectedCount detector (opticalPopulation r)

-- Positivity, finite linewidth, photon-Poisson parameters, and a
-- frequency-dependent W(delta) are not consequences of this rate algebra.
