{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkJacobsonFlat31RigidityBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Quantum.QuantumBirthmarkJacobsonNullConeRecoveryExact as Recovery

------------------------------------------------------------------------
-- FLAT 3+1 NULL-CONE RIGIDITY CROSS-KERNEL BOUNDARY
--
-- The Agda repository owns a concrete finite 1+3 signature carrier, but that
-- owner is a sign/connection model over TriTruth rather than the real vector
-- space needed for the algebraic null-cone rigidity theorem.
--
-- Native dashi_lean4 PR #68 now source-writes the missing real-algebra theorem:
-- for a symmetric 4x4 tensor T over R, if T_ab k^a k^b = 0 for every
-- Minkowski-null k, then T is a scalar multiple of diag(-1,1,1,1).  Its proof
-- uses coordinate null pairs and rational 3-4-5 null directions, then feeds
-- that result into the generic null-cone recovery compiler.
--
-- This module records the exact cross-kernel boundary.  It does not pretend a
-- Lean source file is an Agda proof term, and it does not identify a physical
-- tangent fibre with the flat coordinate carrier without an explicit frame.
------------------------------------------------------------------------

record Flat31RigidityBoundary : Set where
  constructor flat31RigidityBoundary
  field
    agdaFlat13SignatureCarrierOwned : Bool
    genericNullConeRecoveryCompilerOwned : Bool
    finiteFlat31RigiditySourceWrittenInLean : Bool
    flat31RigidityKernelReceiptStillRequired : Bool
    physicalTangentFrameIdentificationStillRequired : Bool
    continuumFibrewiseNullConeTransportStillRequired : Bool
    smoothGlobalAssemblyStillRequired : Bool
    stressEnergySameObjectStillRequired : Bool

canonicalFlat31RigidityBoundary : Flat31RigidityBoundary
canonicalFlat31RigidityBoundary =
  flat31RigidityBoundary true true true true true true true true

agdaFlat13SignatureCarrierOwned : Bool
agdaFlat13SignatureCarrierOwned = true

genericNullConeRecoveryCompilerOwned : Bool
genericNullConeRecoveryCompilerOwned = Recovery.tensorRecoveryCompilerOwned

finiteFlat31RigiditySourceWrittenInLean : Bool
finiteFlat31RigiditySourceWrittenInLean = true

flat31RigidityKernelReceiptStillRequired : Bool
flat31RigidityKernelReceiptStillRequired = true

physicalTangentFrameIdentificationStillRequired : Bool
physicalTangentFrameIdentificationStillRequired = true

continuumFibrewiseNullConeTransportStillRequired : Bool
continuumFibrewiseNullConeTransportStillRequired = true

smoothGlobalAssemblyStillRequired : Bool
smoothGlobalAssemblyStillRequired = true

stressEnergySameObjectStillRequired : Bool
stressEnergySameObjectStillRequired = true

flatCarrierScope : String
flatCarrierScope =
  "DASHI.Geometry.FlatLorentzianModel supplies a finite named 1+3 signature carrier and zero Cartesian connection; it is not itself a real tangent-space/tetrad construction."

leanProducerScope : String
leanProducerScope =
  "dashi_lean4 Synthesis.JacobsonNullConeRigidity proves the flat real 3+1 symmetric-tensor null-cone rigidity statement at source level, and Synthesis.JacobsonFlat31RigidityAdapter instantiates the generic tensor-recovery compiler. Exact-head Lean kernel receipt remains separate."

continuumBoundary : String
continuumBoundary =
  "To use flat null-cone rigidity in Jacobson's continuum argument, one still needs a same-object Lorentz frame/tetrad identification of each physical tangent fibre with the flat carrier, transport of the null-contracted defect through that frame, and any smooth/global assembly required by the selected spacetime model."
