{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkJacobsonHorizonFluxAreaBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source / theorem boundary
--
-- Jacobson 1995 uses an approximate local boost Killing field and affine null
-- generator so that, near the local horizon,
--
--   chi^a = - kappa * lambda * k^a,
--
-- and the matter heat flux becomes proportional to
--
--   - kappa * lambda * T_ab k^a k^b.
--
-- The local-equilibrium Raychaudhuri step gives, to retained first order,
--
--   theta(lambda) ~= - lambda * R_ab k^a k^b,
--
-- hence the area variation carries the same affine factor lambda.
--
-- Sibling Lean PR #68 now source-writes these two scalar reductions and welds
-- them to the existing Clausius integrand conventions. This Agda owner records
-- that cross-kernel theorem authority only; it does not fabricate the physical
-- continuum horizon, boost field, affine measure, stress tensor or remainder
-- control.
------------------------------------------------------------------------

data SourceAuthority : Set where
  Jacobson1995 : SourceAuthority

sourceTitle : SourceAuthority -> String
sourceTitle Jacobson1995 =
  "Thermodynamics of Spacetime: The Einstein Equation of State"

sourceDOI : SourceAuthority -> String
sourceDOI Jacobson1995 = "10.1103/PhysRevLett.75.1260"

record HorizonFluxAreaReductionBoundary : Set where
  constructor horizonFluxAreaReductionBoundary
  field
    horizonFluxReductionSourceWritten : Bool
    linearizedAreaReductionSourceWritten : Bool
    commonAffineFactorExposed : Bool
    physicalBoostKillingFieldStillRequired : Bool
    physicalAffineGeneratorStillRequired : Bool
    physicalHorizonMeasureStillRequired : Bool
    sameObjectStressTensorStillRequired : Bool
    physicalNullCongruenceStillRequired : Bool
    continuumHigherOrderControlStillRequired : Bool

canonicalBoundary : HorizonFluxAreaReductionBoundary
canonicalBoundary =
  horizonFluxAreaReductionBoundary
    true true true true true true true true true

horizonFluxReductionSourceWritten : Bool
horizonFluxReductionSourceWritten = true

linearizedAreaReductionSourceWritten : Bool
linearizedAreaReductionSourceWritten = true

physicalBoostKillingFieldStillRequired : Bool
physicalBoostKillingFieldStillRequired = true

physicalHorizonMeasureStillRequired : Bool
physicalHorizonMeasureStillRequired = true

continuumHigherOrderControlStillRequired : Bool
continuumHigherOrderControlStillRequired = true

statusStatement : String
statusStatement =
  "The Jacobson near-horizon scalar reductions chi=-kappa*lambda*k and theta=-lambda*R_kk, together with their exact factorisation into the existing Clausius heat/area integrands, are source-written in sibling Lean. Remaining work is same-object physical construction of the local boost Killing field, affine null generator and horizon measure, stress-energy attachment, continuum null-congruence theorem, and higher-order control."

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

scalarFluxReductionDoesNotConstructPhysicalHorizon : Bool
scalarFluxReductionDoesNotConstructPhysicalHorizon = true

linearizedAreaReductionDoesNotProveContinuumRaychaudhuri : Bool
linearizedAreaReductionDoesNotProveContinuumRaychaudhuri = true

commonAffineFactorDoesNotProveClausiusPhysically : Bool
commonAffineFactorDoesNotProveClausiusPhysically = true

birthmarkMemoryDoesNotIdentifyHorizonHeatFlux : Bool
birthmarkMemoryDoesNotIdentifyHorizonHeatFlux = true

rtEntropyDoesNotIdentifyHorizonEntropy : Bool
rtEntropyDoesNotIdentifyHorizonEntropy = true
