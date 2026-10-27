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
-- Native dashi_lean4 PR #68 now source-writes:
--   1. the real flat 3+1 rigidity theorem;
--   2. the generic Jacobson null-cone compiler instantiated on that carrier;
--   3. a Lorentz-frame transport compiler showing that any supplied
--      same-object frame/tetrad equivalence preserving quadratic form, tensor
--      contraction and metric multiples inherits the flat theorem.
--
-- This module records the exact cross-kernel boundary.  It does not pretend a
-- Lean source file is an Agda proof term, and it does not manufacture the
-- physical tangent frame or its smooth/global assembly.
------------------------------------------------------------------------

record Flat31RigidityBoundary : Set where
  constructor flat31RigidityBoundary
  field
    agdaFlat13SignatureCarrierOwned : Bool
    genericNullConeRecoveryCompilerOwned : Bool
    finiteFlat31RigiditySourceWrittenInLean : Bool
    lorentzFrameTransportCompilerSourceWrittenInLean : Bool
    flat31RigidityKernelReceiptStillRequired : Bool
    physicalTangentFrameIdentificationStillRequired : Bool
    frameSmoothnessOrGlobalAssemblyStillRequired : Bool
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

lorentzFrameTransportCompilerSourceWrittenInLean : Bool
lorentzFrameTransportCompilerSourceWrittenInLean = true

flat31RigidityKernelReceiptStillRequired : Bool
flat31RigidityKernelReceiptStillRequired = true

physicalTangentFrameIdentificationStillRequired : Bool
physicalTangentFrameIdentificationStillRequired = true

frameSmoothnessOrGlobalAssemblyStillRequired : Bool
frameSmoothnessOrGlobalAssemblyStillRequired = true

-- Backwards-compatible broad name: the algebraic transport compiler is now
-- source-written, so what remains is construction/identification of the frame.
continuumFibrewiseNullConeTransportStillRequired : Bool
continuumFibrewiseNullConeTransportStillRequired = true

stressEnergySameObjectStillRequired : Bool
stressEnergySameObjectStillRequired = true

flatCarrierScope : String
flatCarrierScope =
  "DASHI.Geometry.FlatLorentzianModel supplies a finite named 1+3 signature carrier and zero Cartesian connection; it is not itself a real tangent-space/tetrad construction."

leanProducerScope : String
leanProducerScope =
  "dashi_lean4 Synthesis.JacobsonNullConeRigidity proves flat real 3+1 symmetric-tensor null-cone rigidity at source level; Synthesis.JacobsonFlat31RigidityAdapter instantiates the generic tensor-recovery compiler; Synthesis.JacobsonNullConeRigidityTransport transports rigidity through a supplied Lorentz-frame equivalence. Exact-head Lean kernel receipt remains separate."

continuumBoundary : String
continuumBoundary =
  "After the frame-transport compiler, the continuum rigidity residual is no longer a second null-cone theorem. The live payment is construction and same-object identification of a physical Lorentz frame/tetrad on each selected tangent fibre, compatibility with the field-equation tensor contraction, and any smooth/global assembly needed by the spacetime model."
