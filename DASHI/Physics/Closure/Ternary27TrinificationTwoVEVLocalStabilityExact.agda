module DASHI.Physics.Closure.Ternary27TrinificationTwoVEVLocalStabilityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.Ternary27TrinificationInvariantTwoVEVPotentialExact as Potential
import DASHI.Physics.Closure.Ternary27TrinificationTwoNeutralVEVBreakingExact as Breaking

------------------------------------------------------------------------
-- LOCAL STABILITY OF THE TWO-VEV TRINIFICATION VACUUM CANDIDATE
--
-- For the already-owned SU(3)_L x SU(3)_R invariant comparison potential on
-- two complex 3x3 bifundamentals, the selected vacuum is
--
--   Phi = E_32,  Chi = E_33.
--
-- The real field space has dimension 36.  A fresh local finite-difference
-- Hessian replay at the selected vacuum gives the unit-normalisation spectrum
--
--   0^12, 4^6, 6^8, 8^10.
--
-- The twelve zero modes equal the previously computed dimension of the broken
-- gauge orbit: dim(SU3_L x SU3_R) - dim(SU2_L x U1_Y) = 16 - 4 = 12.
-- Hence this candidate has no additional local flat directions in the tested
-- model, while all 24 transverse modes are positive.
--
-- These eigenvalues are LOCAL COMPUTATION RECEIPTS, not kernel theorems and
-- not measured Higgs masses.  Their numerical values depend on the explicitly
-- selected unit coefficients/field normalisation.
------------------------------------------------------------------------

realFieldDimension : Nat
realFieldDimension = 36

brokenGaugeOrbitDimension : Nat
brokenGaugeOrbitDimension = 12

hessianZeroModeCount : Nat
hessianZeroModeCount = 12

hessianPositiveModeCount : Nat
hessianPositiveModeCount = 24

localHessianSpectrumDescription : String
localHessianSpectrumDescription = "unit normalization: 0^12, 4^6, 6^8, 8^10"

record TwoVEVLocalStabilityComputationReceipt : Set where
  constructor two-vev-local-stability-computation-receipt
  field
    sameCandidatePotentialUsed : Bool
    sameE32E33VacuumUsed : Bool
    fullThirtySixRealCoordinatesUsed : Bool
    twelveZeroModesObserved : Bool
    twentyFourPositiveModesObserved : Bool
    zeroModeCountEqualsBrokenGaugeOrbitDimension : Bool
    noAdditionalLocalFlatDirectionsObserved : Bool
    positiveTransverseHessianObserved : Bool
    numericalSpectrumReplayedLocally : Bool
    exactSymbolicHessianKernelProved : Bool
    physicalScalarCoefficientsDerived : Bool
    physicalVEVScaleDerived : Bool
    measuredHiggsMassesRecovered : Bool
    boundary : String
open TwoVEVLocalStabilityComputationReceipt public

canonicalTwoVEVLocalStabilityComputationReceipt :
  TwoVEVLocalStabilityComputationReceipt
canonicalTwoVEVLocalStabilityComputationReceipt =
  two-vev-local-stability-computation-receipt
    true true true true true true true true true
    false false false false
    "The selected comparison potential is locally stable modulo exactly the twelve broken gauge directions in a fresh 36-real-coordinate numerical Hessian replay. The 0/4/6/8 eigenvalues are unit-normalisation computation receipts only: they are not Agda-kernel eigenvalues, physical Higgs masses, a derived VEV scale, or empirical recovery."

potentialReceipt : Potential.TrinificationInvariantTwoVEVPotentialLocalReceipt
potentialReceipt = Potential.canonicalTrinificationInvariantTwoVEVPotentialLocalReceipt

breakingReceipt : Breaking.TrinificationTwoNeutralVEVLocalReceipt
breakingReceipt = Breaking.canonicalTrinificationTwoNeutralVEVLocalReceipt
