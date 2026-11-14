{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkJacobsonLocalFrameFieldCompilerBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Cross-kernel theorem boundary
--
-- Sibling Lean PR #68 now composes the already-paid Jacobson scalar/null-cone
-- algebra into a single point-indexed local-Lorentz-frame compiler.
--
-- A supplied physical package contains, at every point p:
--   * local Lorentz components of one Ricci tensor R_ab(p),
--   * local Lorentz components of one stress tensor T_ab(p),
--   * a nonzero local boost/surface-gravity scale kappa(p),
--   * the same-object Clausius equality for every null direction.
--
-- From those inputs Lean constructs a field phi(p) satisfying pointwise
--
--   R_ab(p) - 8*pi*G*T_ab(p) = phi(p) g_ab.
--
-- This Agda module records that theorem-source boundary.  It does NOT identify
-- a physical frame, horizon/QFT state, Ricci/stress fields, smoothness of phi,
-- or a global continuum Einstein solution.
------------------------------------------------------------------------

record LocalFrameFieldCompilerBoundary : Set where
  constructor localFrameFieldCompilerBoundary
  field
    localFrameFieldCompilerSourceWritten : Bool
    pointIndexedPhiFieldSourceWritten : Bool
    sameObjectRicciStressRelationSourceWritten : Bool
    physicalLocalLorentzFrameStillRequired : Bool
    physicalClausiusSameObjectStillRequired : Bool
    physicalRicciStressIdentificationStillRequired : Bool
    recoveredPhiRegularityStillRequired : Bool
    continuumGlobalAttachmentStillRequired : Bool

canonicalBoundary : LocalFrameFieldCompilerBoundary
canonicalBoundary =
  localFrameFieldCompilerBoundary
    true true true true true true true true

localFrameFieldCompilerSourceWritten : Bool
localFrameFieldCompilerSourceWritten = true

pointIndexedPhiFieldSourceWritten : Bool
pointIndexedPhiFieldSourceWritten = true

physicalLocalLorentzFrameStillRequired : Bool
physicalLocalLorentzFrameStillRequired = true

physicalClausiusSameObjectStillRequired : Bool
physicalClausiusSameObjectStillRequired = true

recoveredPhiRegularityStillRequired : Bool
recoveredPhiRegularityStillRequired = true

statusStatement : String
statusStatement =
  "Sibling Lean composes the local Clausius relation, 8*pi*G normalization and flat 3+1 null-cone rigidity into a point-indexed field theorem R_ab(p)-8*pi*G*T_ab(p)=phi(p)g_ab, and constructs phi as an actual field. Remaining work is physical local-frame/QFT/horizon construction, same-object Ricci/stress identification, regularity of phi, and continuum/global solution attachment."

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

pointIndexedCompilerDoesNotConstructPhysicalFrame : Bool
pointIndexedCompilerDoesNotConstructPhysicalFrame = true

pointIndexedCompilerDoesNotProveClausiusPhysically : Bool
pointIndexedCompilerDoesNotProveClausiusPhysically = true

pointwisePhiDoesNotImplySmoothPhi : Bool
pointwisePhiDoesNotImplySmoothPhi = true

pointwiseEinsteinRelationDoesNotImplyGlobalSolution : Bool
pointwiseEinsteinRelationDoesNotImplyGlobalSolution = true

birthmarkMemoryDoesNotIdentifyStressEnergy : Bool
birthmarkMemoryDoesNotIdentifyStressEnergy = true
