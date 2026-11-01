module DASHI.Physics.Closure.NSPeriodicConcreteFullOperatorReceipt where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Exact finite receipt for the full polarized K = 2, R = 2 operator diagnostic.
--
-- The finite weighted-l1 matrix includes two transverse polarizations,
-- Biot--Savart, the linearized vorticity triad, output Leray projection, the
-- dyadic commutator and exact convolution multiplicity.
------------------------------------------------------------------------

fullOperatorCheckedInteractions : Nat
fullOperatorCheckedInteractions = 221360

fullOperatorNonzeroEntries : Nat
fullOperatorNonzeroEntries = 110680

fullOperatorRowNumerator fullOperatorRowDenominator : Nat
fullOperatorRowNumerator = 16863287437
fullOperatorRowDenominator = 253834854

fullOperatorColumnNumerator fullOperatorColumnDenominator : Nat
fullOperatorColumnNumerator = 274
fullOperatorColumnDenominator = 7

fullOperatorSchurNumerator fullOperatorSchurDenominator : Nat
fullOperatorSchurNumerator = 2310270378869
fullOperatorSchurDenominator = 888421989

fullOperatorInteractionRegression :
  fullOperatorCheckedInteractions ≡ 221360
fullOperatorInteractionRegression = refl

fullOperatorEntryRegression :
  fullOperatorNonzeroEntries ≡ 110680
fullOperatorEntryRegression = refl

finiteWeightedL1EqualsOfficialNorm : Bool
finiteWeightedL1EqualsOfficialNorm = false

cutoffUniformFullOperatorBoundProved : Bool
cutoffUniformFullOperatorBoundProved = false

universalFarLowFromFullOperatorReceipt : Bool
universalFarLowFromFullOperatorReceipt = false
