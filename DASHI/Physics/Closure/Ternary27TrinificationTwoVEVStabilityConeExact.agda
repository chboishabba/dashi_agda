module DASHI.Physics.Closure.Ternary27TrinificationTwoVEVStabilityConeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.Ternary27TrinificationInvariantTwoVEVPotentialExact as Potential
import DASHI.Physics.Closure.Ternary27TrinificationTwoVEVLocalStabilityExact as Local

------------------------------------------------------------------------
-- SIX-COEFFICIENT LOCAL STABILITY CONE
--
-- Give independent coefficients (a,b,c,d,e,f) to the six invariant comparison
-- terms of the existing two-bifundamental potential.  A local Hessian analysis
-- at (Phi,Chi)=(E32,E33) shows that the six term Hessians commute there and the
-- common spectral families are
--
--   0^12,
--   (8a)^1, (8b)^1,
--   (4e)^2, (4f)^4,
--   (4c+2f)^4, (4d+2f)^4,
--   (4c+2e+2f)^4, (4d+2e+2f)^4.
--
-- Therefore the simple strict cone
--
--   a,b,e,f > 0,
--   2c+f > 0,
--   2d+f > 0
--
-- makes every transverse mode positive; with e>0 the last two displayed
-- families are then automatically positive.  The twelve zero modes are the
-- broken gauge orbit already identified in the same-subspace local receipt.
--
-- This is a LOCAL COMPUTATION RECEIPT.  It reduces the candidate parameter
-- space but does not select coefficients, VEV scale, couplings or measured
-- scalar masses.
------------------------------------------------------------------------

zeroModeMultiplicity : Nat
zeroModeMultiplicity = 12

transverseModeCount : Nat
transverseModeCount = 24

spectralFamilies : String
spectralFamilies =
  "0^12,(8a)^1,(8b)^1,(4e)^2,(4f)^4,(4c+2f)^4,(4d+2f)^4,(4c+2e+2f)^4,(4d+2e+2f)^4"

strictStabilityCone : String
strictStabilityCone = "a>0,b>0,e>0,f>0,2c+f>0,2d+f>0"

record TwoVEVStabilityConeComputationReceipt : Set where
  constructor two-vev-stability-cone-computation-receipt
  field
    sameSixInvariantTermsUsed : Bool
    sameE32E33VacuumUsed : Bool
    individualTermHessiansComputed : Bool
    termHessiansCommuteAtVacuum : Bool
    twelveGaugeZeroModesRetained : Bool
    eightTransverseEigenvalueFamiliesRecovered : Bool
    thirtyRandomCoefficientReplaysMatchedFormula : Bool
    simpleStrictStabilityConeExtracted : Bool
    stabilityConeSelectsUniquePotential : Bool
    physicalCoefficientsDerived : Bool
    vevScaleDerived : Bool
    measuredScalarSpectrumRecovered : Bool
    exactSymbolicHessianKernelProved : Bool
    boundary : String
open TwoVEVStabilityConeComputationReceipt public

canonicalTwoVEVStabilityConeComputationReceipt : TwoVEVStabilityConeComputationReceipt
canonicalTwoVEVStabilityConeComputationReceipt =
  two-vev-stability-cone-computation-receipt
    true true true true true true true true
    false false false false false
    "The local computation classifies the Hessian of the six-coefficient invariant comparison potential at the selected two-VEV vacuum and extracts a strict positivity cone modulo the twelve broken gauge directions. It does not choose a unique potential or physical coefficients/scale and is not represented as an Agda-kernel eigensystem proof."

potentialReceipt : Potential.TrinificationInvariantTwoVEVPotentialLocalReceipt
potentialReceipt = Potential.canonicalTrinificationInvariantTwoVEVPotentialLocalReceipt

localStabilityReceipt : Local.TwoVEVLocalStabilityComputationReceipt
localStabilityReceipt = Local.canonicalTwoVEVLocalStabilityComputationReceipt
