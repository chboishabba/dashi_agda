module DASHI.Physics.YangMills.BalabanMarkedSourceCoefficientEnergyHilbertCompilerExact where

------------------------------------------------------------------------
-- ROUND88: DIFFERENTIATED LOCALIZATION -> COEFFICIENT ENERGY -> HILBERT MODULUS
--
-- PRIMARY SOURCE / CALIBRATION
--
-- Augustin-Louis Cauchy and Hermann Amandus Schwarz,
-- finite weighted Cauchy--Schwarz inequality. Classical result; no DOI.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- DASHI CROSS-POLLINATION
--
-- The Navier--Stokes lane already proves finite weighted Cauchy--Schwarz from
-- the exact weighted Gram-defect identity rather than importing it as an
-- authority.  Reuse that theorem here.  A differentiated local source
-- functional with coefficient samples a_x and test samples f_x obeys
--
--   (sum_x w_x a_x f_x)^2
--     <= (sum_x w_x a_x^2) (sum_x w_x f_x^2).
--
-- Consequently Round87 B4/B5 are NOT independent analytic miracles once the
-- literal CMP116 differentiated source is represented by finite/localized
-- coefficient samples.  Both the composite and stress Hilbert moduli reduce to
-- the SAME physical estimate:
--
--   cutoff-uniform weighted coefficient energy <= C^2.
--
-- CMP116 supplies the analytic mechanism for exponentially localized
-- differentiated coefficients.  What remains physical is the same-object
-- identification plus a uniform geometric/shell square-summability bound.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_; _*_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteWeightedCauchyExact as Cauchy

record FiniteMarkedSourceHilbertData : Set₁ where
  field
    samples : List Cauchy.WeightedPair
    coefficientEnergyCap : ℚ
    coefficientEnergyBound :
      Cauchy.leftEnergy samples ≤ coefficientEnergyCap
open FiniteMarkedSourceHilbertData public

sourcePairing : FiniteMarkedSourceHilbertData → ℚ
sourcePairing dataSet = Cauchy.weightedPairing (samples dataSet)

testHilbertEnergy : FiniteMarkedSourceHilbertData → ℚ
testHilbertEnergy dataSet = Cauchy.rightEnergy (samples dataSet)

sourceCoefficientEnergy : FiniteMarkedSourceHilbertData → ℚ
sourceCoefficientEnergy dataSet = Cauchy.leftEnergy (samples dataSet)

sourcePairingSquaredCauchy :
  (dataSet : FiniteMarkedSourceHilbertData) →
  let selected = samples dataSet in
  L2.square (Cauchy.weightedPairing selected)
  ≤ Cauchy.leftEnergy selected * Cauchy.rightEnergy selected
sourcePairingSquaredCauchy dataSet =
  Cauchy.finiteWeightedCauchy (samples dataSet)

------------------------------------------------------------------------
-- A paired carrier makes the intended coefficient/test interpretation explicit
-- without re-proving the Gram identity.
------------------------------------------------------------------------

record MarkedCoefficientTestSample : Set where
  constructor markedCoefficientTestSample
  field
    weight coefficient testValue : ℚ
    weightNonnegative : 0ℚ ≤ weight
open MarkedCoefficientTestSample public

asWeightedPair : MarkedCoefficientTestSample → Cauchy.WeightedPair
asWeightedPair sample = Cauchy.weighted-pair
  (weight sample)
  (coefficient sample)
  (testValue sample)
  (weightNonnegative sample)

-- The exact Cauchy step itself is fully machine checked.  The remaining
-- Yang--Mills producer is now coefficient-energy control, not an abstract
-- continuity receipt.
markedSourceCoefficientEnergyToHilbertCauchyLevel : ProofLevel
markedSourceCoefficientEnergyToHilbertCauchyLevel = machineChecked

-- Physical seam shared by curvature/composite and stress marks: identify the
-- literal differentiated CMP116 source coefficients and prove their weighted
-- square energy is cutoff/volume/scale uniformly bounded.  Exponential
-- localization is expected to feed this through a geometric shell sum, but no
-- such nonperturbative same-object estimate is asserted here.
physicalCMP116UniformMarkedCoefficientEnergyLevel : ProofLevel
physicalCMP116UniformMarkedCoefficientEnergyLevel = conditional
