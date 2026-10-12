{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkJacobsonCouplingNormalizationBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Foundations.EntropicGravitySourceBoundaryExact as Sources

------------------------------------------------------------------------
-- JACOBSON COUPLING NORMALIZATION CROSS-KERNEL BOUNDARY
--
-- Jacobson's 1995 derivation uses the local Unruh normalization
--
--   T = hbar kappa / (2 pi)
--
-- together with horizon entropy density eta = dS/dA.  At the null-contracted
-- algebraic stage the curvature/stress coefficient is
--
--   2 pi / (hbar eta).
--
-- Native dashi_lean4 PR #68 now source-writes the exact field algebra showing
-- that substituting the Bekenstein-Hawking normalization
--
--   eta = 1 / (4 hbar G)
--
-- gives exactly 8 pi G.  This owner does not treat that arithmetic theorem as
-- an Agda proof term, and it does not manufacture the physical Unruh, area-law,
-- Raychaudhuri, or stress-energy receipts required by Jacobson's argument.
------------------------------------------------------------------------

record JacobsonCouplingNormalizationBoundary : Set where
  constructor jacobsonCouplingNormalizationBoundary
  field
    jacobson1995SourceBoundaryOwned : Bool
    jacobsonCouplingAlgebraSourceWrittenInLean : Bool
    eightPiGSpecializationSourceWrittenInLean : Bool
    couplingAlgebraKernelReceiptStillRequired : Bool
    unruhNormalizationPhysicalReceiptStillRequired : Bool
    entropyAreaPhysicalReceiptStillRequired : Bool
    raychaudhuriSameCarrierStillRequired : Bool
    stressEnergySameObjectStillRequired : Bool

canonicalJacobsonCouplingNormalizationBoundary :
  JacobsonCouplingNormalizationBoundary
canonicalJacobsonCouplingNormalizationBoundary =
  jacobsonCouplingNormalizationBoundary
    true true true true true true true true

jacobson1995SourceBoundaryOwned : Bool
jacobson1995SourceBoundaryOwned = true

jacobsonCouplingAlgebraSourceWrittenInLean : Bool
jacobsonCouplingAlgebraSourceWrittenInLean = true

eightPiGSpecializationSourceWrittenInLean : Bool
eightPiGSpecializationSourceWrittenInLean = true

couplingAlgebraKernelReceiptStillRequired : Bool
couplingAlgebraKernelReceiptStillRequired = true

unruhNormalizationPhysicalReceiptStillRequired : Bool
unruhNormalizationPhysicalReceiptStillRequired = true

entropyAreaPhysicalReceiptStillRequired : Bool
entropyAreaPhysicalReceiptStillRequired = true

raychaudhuriSameCarrierStillRequired : Bool
raychaudhuriSameCarrierStillRequired = true

stressEnergySameObjectStillRequired : Bool
stressEnergySameObjectStillRequired = true

normalizationStatement : String
normalizationStatement =
  "Native Lean source proves (2*pi)/(hbar*eta) = 8*pi*G after eta = 1/(4*hbar*G), under nonzero hbar and G. This is coefficient algebra only."

physicalBoundary : String
physicalBoundary =
  "The 8*pi*G arithmetic does not prove the Unruh temperature law, the Bekenstein-Hawking area density on the selected local horizon, continuum Raychaudhuri focusing, or identification of heat flux with the same stress-energy tensor."
