{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkJacobsonRaychaudhuriEquilibriumBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Gravity.NullRaychaudhuriSachsFocusingExact as Raychaudhuri

------------------------------------------------------------------------
-- RAYCHAUDHURI LOCAL-EQUILIBRIUM CROSS-KERNEL BOUNDARY
--
-- Existing Agda authority already records the continuum null-Raychaudhuri /
-- Sachs equation as a source-backed target rather than a locally derived
-- continuum theorem. Sibling Lean now pays the scalar specialization used in
-- Jacobson's local horizon argument:
--
--   theta = 0, shear = 0, twist = 0  =>  d theta / d lambda = - R_kk
--
-- and welds the factored first-order area coefficient to the existing
-- Clausius `areaVariationIntegrand = -R_kk` convention.
--
-- This owner records that narrower payment without promoting the continuum
-- congruence equation, horizon equilibrium identification, or higher-order
-- control.
------------------------------------------------------------------------

record RaychaudhuriEquilibriumCrossKernelBoundary : Set where
  constructor raychaudhuriEquilibriumCrossKernelBoundary
  field
    raychaudhuriAuthorityOwnerReused : Bool
    equilibriumRaychaudhuriAlgebraSourceWritten : Bool
    factoredAreaCoefficientWeldSourceWritten : Bool
    physicalNullCongruenceEquationStillRequired : Bool
    localEquilibriumIdentificationStillRequired : Bool
    hypersurfaceOrthogonalityStillRequired : Bool
    higherOrderControlStillRequired : Bool
    sameCarrierRicciIdentificationStillRequired : Bool
    scalarEquilibriumAlgebraDoesNotProveContinuumGeometry : Bool
    scope : String

canonicalRaychaudhuriEquilibriumCrossKernelBoundary :
  RaychaudhuriEquilibriumCrossKernelBoundary
canonicalRaychaudhuriEquilibriumCrossKernelBoundary =
  raychaudhuriEquilibriumCrossKernelBoundary
    true
    true
    true
    true
    true
    true
    true
    true
    true
    "Sibling Lean pays the local-equilibrium Raychaudhuri scalar algebra and the factored area-coefficient weld. The physical null-congruence equation, hypersurface orthogonality, vanishing initial expansion/shear, same-carrier Ricci identification and higher-order control remain separate continuum receipts."

equilibriumRaychaudhuriAlgebraSourceWritten : Bool
equilibriumRaychaudhuriAlgebraSourceWritten = true

physicalNullCongruenceEquationStillRequired : Bool
physicalNullCongruenceEquationStillRequired = true

localEquilibriumIdentificationStillRequired : Bool
localEquilibriumIdentificationStillRequired = true

hypersurfaceOrthogonalityStillRequired : Bool
hypersurfaceOrthogonalityStillRequired = true

higherOrderControlStillRequired : Bool
higherOrderControlStillRequired = true

sameCarrierRicciIdentificationStillRequired : Bool
sameCarrierRicciIdentificationStillRequired = true
