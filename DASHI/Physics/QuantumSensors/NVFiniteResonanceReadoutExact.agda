module DASHI.Physics.QuantumSensors.NVFiniteResonanceReadoutExact where

-- A symbolic finite NV resonant frequency readout.
-- No claim that a resolved ODMR line, optical emission probability, linewidth,
-- or actual experimental calibration has been derived.
-- Reuses the exact axial spin-1 finite qutrit owner.

open import Agda.Builtin.Equality using (_≡_; refl; cong)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
import DASHI.Algebra.Quantum.FiniteQutrit as Q
import DASHI.Physics.QuantumSensors.NVSpinOneAxialExact as NV

record FiniteResonance : Set where
  constructor finite-resonance
  field
    model : NV.AxialNV
    microwaveReference : ℚ
open FiniteResonance public

transitionPlus transitionMinus : FiniteResonance → ℚ
transitionPlus r = NV.energy (model r) Q.ket0 - NV.energy (model r) Q.ket1
transitionMinus r = NV.energy (model r) Q.ket2 - NV.energy (model r) Q.ket1

signedBranchDifference : FiniteResonance → ℚ
signedBranchDifference r = NV.signedSplitting (model r)

-- A readout datum retains the labelled theoretical frequencies and calibration
-- reference, not an invented photon count or a measured resonance.
record SymbolicODMRDatum : Set where
  constructor symbolic-odmr
  field
    plusFrequency : ℚ
    minusFrequency : ℚ
    referenceFrequency : ℚ
open SymbolicODMRDatum public

predictODMR : FiniteResonance → SymbolicODMRDatum
predictODMR r = symbolic-odmr
  (transitionPlus r) (transitionMinus r) (microwaveReference r)

predictPlusCorrect :
  (r : FiniteResonance) →
  plusFrequency (predictODMR r) ≡ transitionPlus r
predictPlusCorrect r = refl

predictMinusCorrect :
  (r : FiniteResonance) →
  minusFrequency (predictODMR r) ≡ transitionMinus r
predictMinusCorrect r = refl
