{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkJacobsonCouplingNormalizationBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.EntropicGravitySourceBoundaryExact as Sources

------------------------------------------------------------------------
-- JACOBSON COUPLING / CLAUSIUS NULL-ALGEBRA CROSS-KERNEL BOUNDARY
--
-- Jacobson's 1995 derivation uses local Unruh temperature
--
--   T = hbar kappa / (2 pi)
--
-- horizon entropy density eta = dS/dA, heat-flux integrand
--
--   -kappa T_ab k^a k^b,
--
-- and the linearised area-variation integrand
--
--   -R_ab k^a k^b.
--
-- Native dashi_lean4 PR #68 now source-writes two exact algebraic layers:
--
--   1. (2 pi)/(hbar eta) specializes to 8 pi G after
--      eta = 1/(4 hbar G);
--   2. once the same-object heat-flux, Unruh, entropy-area and Raychaudhuri
--      integrands are supplied, Clausius equality cancels the common boost
--      parameter and yields the null-contracted curvature/stress relation,
--      with the Bekenstein-Hawking specialization giving 8 pi G.
--
-- These are coefficient/scalar theorems only.  This owner does not turn them
-- into Agda proof terms or manufacture the physical QFT/geometry premises.
------------------------------------------------------------------------

record JacobsonCouplingNormalizationBoundary : Set where
  constructor jacobsonCouplingNormalizationBoundary
  field
    jacobson1995SourceBoundaryOwned : Bool
    jacobsonCouplingAlgebraSourceWrittenInLean : Bool
    eightPiGSpecializationSourceWrittenInLean : Bool
    clausiusNullAlgebraSourceWrittenInLean : Bool
    couplingAlgebraKernelReceiptStillRequired : Bool
    unruhNormalizationPhysicalReceiptStillRequired : Bool
    entropyAreaPhysicalReceiptStillRequired : Bool
    geometricHeatFluxReceiptStillRequired : Bool
    raychaudhuriSameCarrierStillRequired : Bool
    stressEnergySameObjectStillRequired : Bool

canonicalJacobsonCouplingNormalizationBoundary :
  JacobsonCouplingNormalizationBoundary
canonicalJacobsonCouplingNormalizationBoundary =
  jacobsonCouplingNormalizationBoundary
    true true true true true true true true true true

jacobson1995SourceBoundaryOwned : Bool
jacobson1995SourceBoundaryOwned = true

jacobsonCouplingAlgebraSourceWrittenInLean : Bool
jacobsonCouplingAlgebraSourceWrittenInLean = true

eightPiGSpecializationSourceWrittenInLean : Bool
eightPiGSpecializationSourceWrittenInLean = true

clausiusNullAlgebraSourceWrittenInLean : Bool
clausiusNullAlgebraSourceWrittenInLean = true

couplingAlgebraKernelReceiptStillRequired : Bool
couplingAlgebraKernelReceiptStillRequired = true

unruhNormalizationPhysicalReceiptStillRequired : Bool
unruhNormalizationPhysicalReceiptStillRequired = true

entropyAreaPhysicalReceiptStillRequired : Bool
entropyAreaPhysicalReceiptStillRequired = true

geometricHeatFluxReceiptStillRequired : Bool
geometricHeatFluxReceiptStillRequired = true

raychaudhuriSameCarrierStillRequired : Bool
raychaudhuriSameCarrierStillRequired = true

stressEnergySameObjectStillRequired : Bool
stressEnergySameObjectStillRequired = true

normalizationStatement : String
normalizationStatement =
  "Native Lean source proves (2*pi)/(hbar*eta) = 8*pi*G after eta = 1/(4*hbar*G), and separately proves that same-object Clausius equality reduces the supplied heat-flux/area-variation integrands to the corresponding null-contracted Einstein coefficient."

physicalBoundary : String
physicalBoundary =
  "The scalar cancellation does not prove the Unruh temperature law, the Bekenstein-Hawking area density on the selected local horizon, the geometric heat-flux identification, continuum Raychaudhuri focusing, or identification of heat flux with the same physical stress-energy tensor."
