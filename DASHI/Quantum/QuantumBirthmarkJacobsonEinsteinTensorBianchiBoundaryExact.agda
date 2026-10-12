{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkJacobsonEinsteinTensorBianchiBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.ContractedBianchiMatterClosure as BianchiMatter
import DASHI.Physics.Closure.ContinuumEinsteinMatterSolutionBoundary as Continuum

------------------------------------------------------------------------
-- JACOBSON EINSTEIN-TENSOR / BIANCHI TERMINAL ALGEBRA BOUNDARY
--
-- Native dashi_lean4 PR #68 now source-writes four theorem-bearing layers:
--
--   * same-object flat 3+1 Jacobson composition:
--       Clausius on every null direction
--       -> R_kk = 8 pi G T_kk
--       -> Ricci - 8 pi G Stress = phi metric;
--
--   * pointwise conversion
--       R_ab - C T_ab = phi g_ab
--     ->
--       G_ab + Lambda g_ab = C T_ab,
--     with Lambda = R/2 - phi;
--
--   * Bianchi + stress conservation algebra
--       div Ric = (1/2) dR,
--       div T = 0,
--       div(Ric - C T) = d phi
--     -> d(R/2 - phi) = 0;
--
--   * pinned Mathlib v4.28 zero-fderiv constancy on open preconnected domains.
--
-- The existing Agda ContractedBianchiMatterClosure is reused only as a
-- fail-closed authority/receipt surface.  It explicitly does not supply the
-- missing physical W4 stress-energy authority.  Likewise the continuum
-- Einstein-matter solution owner supplies a solution schema, not physical
-- continuum existence.
------------------------------------------------------------------------

record JacobsonEinsteinTensorBianchiBoundary : Set where
  constructor jacobsonEinsteinTensorBianchiBoundary
  field
    flat31JacobsonEinsteinCompilerSourceWrittenInLean : Bool
    einsteinTensorPointwiseAlgebraSourceWrittenInLean : Bool
    bianchiLambdaGradientCompilerSourceWrittenInLean : Bool
    mathlibZeroDerivativeConstancyOwned : Bool
    agdaContractedBianchiClosureSurfaceOwned : Bool
    agdaContinuumEinsteinMatterSchemaOwned : Bool
    leanKernelReceiptStillRequired : Bool
    physicalLambdaFDerivZeroStillRequired : Bool
    physicalOpenPreconnectedDomainStillRequired : Bool
    sameObjectStressEnergyAuthorityStillRequired : Bool
    continuumEinsteinMatterSolutionAttachmentStillRequired : Bool

canonicalJacobsonEinsteinTensorBianchiBoundary :
  JacobsonEinsteinTensorBianchiBoundary
canonicalJacobsonEinsteinTensorBianchiBoundary =
  jacobsonEinsteinTensorBianchiBoundary
    true true true true true true true true true true true

flat31JacobsonEinsteinCompilerSourceWrittenInLean : Bool
flat31JacobsonEinsteinCompilerSourceWrittenInLean = true

einsteinTensorPointwiseAlgebraSourceWrittenInLean : Bool
einsteinTensorPointwiseAlgebraSourceWrittenInLean = true

bianchiLambdaGradientCompilerSourceWrittenInLean : Bool
bianchiLambdaGradientCompilerSourceWrittenInLean = true

mathlibZeroDerivativeConstancyOwned : Bool
mathlibZeroDerivativeConstancyOwned = true

agdaContractedBianchiClosureSurfaceOwned : Bool
agdaContractedBianchiClosureSurfaceOwned = true

agdaContinuumEinsteinMatterSchemaOwned : Bool
agdaContinuumEinsteinMatterSchemaOwned = true

leanKernelReceiptStillRequired : Bool
leanKernelReceiptStillRequired = true

physicalLambdaFDerivZeroStillRequired : Bool
physicalLambdaFDerivZeroStillRequired = true

physicalOpenPreconnectedDomainStillRequired : Bool
physicalOpenPreconnectedDomainStillRequired = true

sameObjectStressEnergyAuthorityStillRequired : Bool
sameObjectStressEnergyAuthorityStillRequired = true

continuumEinsteinMatterSolutionAttachmentStillRequired : Bool
continuumEinsteinMatterSolutionAttachmentStillRequired = true

flat31CompositionStatement : String
flat31CompositionStatement =
  "On the same flat real 3+1 carrier, native Lean source composes all-null Clausius with the 8*pi*G normalization and null-cone rigidity to obtain Ricci - 8*pi*G Stress = phi metric."

pointwiseAlgebraStatement : String
pointwiseAlgebraStatement =
  "The metric ambiguity from null-cone recovery is algebraically equivalent pointwise to an Einstein-tensor equation with Lambda = R/2 - phi."

bianchiStatement : String
bianchiStatement =
  "Once same-object contracted Bianchi, stress conservation, and divergence of the recovered Ricci-minus-stress relation are supplied, native Lean algebra gives dLambda = 0. Pinned Mathlib then gives constancy on an open preconnected differentiable domain when the physical Lambda field is identified with zero fderiv."

physicalBoundary : String
physicalBoundary =
  "The remaining payment is not finite Jacobson or Einstein-tensor algebra: it is same-object physical stress-energy authority, continuum tangent/frame and differentiability/domain identification, the physical fderiv-zero attachment for Lambda, and a physical continuum Einstein-matter solution on the selected spacetime."
