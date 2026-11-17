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
-- The stronger replay does not rely on 12=12.  It explicitly constructs the
-- sixteen infinitesimal SU(3)_L x SU(3)_R tangent vectors on the SAME ordered
-- pair (Phi,Chi). Their real span has rank 12, the Hessian annihilates that
-- span, and comparison of orthonormal bases by principal angles gives twelve
-- unit singular values.  Thus, numerically on this candidate,
--
--   ker(H_V) = T_v (G . v)
--
-- as the same subspace.  There are no additional observed local flat modes.
--
-- These are LOCAL COMPUTATION RECEIPTS, not Agda-kernel spectral theorems and
-- not measured Higgs masses. Numerical eigenvalues depend on the selected unit
-- coefficients and field/generator normalisation.
------------------------------------------------------------------------

realFieldDimension : Nat
realFieldDimension = 36

brokenGaugeOrbitDimension : Nat
brokenGaugeOrbitDimension = 12

gaugeOrbitTangentRank : Nat
gaugeOrbitTangentRank = 12

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
    fullSixteenLRInfinitesimalGeneratorsUsed : Bool
    gaugeOrbitTangentRankTwelveObserved : Bool
    twelveZeroModesObserved : Bool
    twentyFourPositiveModesObserved : Bool
    zeroModeCountEqualsBrokenGaugeOrbitDimension : Bool
    gaugeOrbitTangentAnnihilatedByHessian : Bool
    principalAngleSameSubspaceCheckPassed : Bool
    hessianKernelEqualsGaugeOrbitTangentLocally : Bool
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
    true true true true true true true true true true true true true true
    false false false false
    "The selected comparison potential is locally stable modulo the actual broken gauge-orbit tangent: a fresh 36-real-coordinate replay gives spectrum 0^12,4^6,6^8,8^10, the sixteen infinitesimal L/R generators span rank 12, the Hessian annihilates that span, and principal-angle comparison identifies it with the Hessian kernel. This is a local numerical same-subspace receipt only, not an Agda-kernel eigenspace theorem, a physical Higgs potential, a VEV scale, or measured masses."

potentialReceipt : Potential.TrinificationInvariantTwoVEVPotentialLocalReceipt
potentialReceipt = Potential.canonicalTrinificationInvariantTwoVEVPotentialLocalReceipt

breakingReceipt : Breaking.TrinificationTwoNeutralVEVLocalReceipt
breakingReceipt = Breaking.canonicalTrinificationTwoNeutralVEVLocalReceipt
