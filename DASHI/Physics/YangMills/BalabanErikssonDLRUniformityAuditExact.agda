module DASHI.Physics.YangMills.BalabanErikssonDLRUniformityAuditExact where

------------------------------------------------------------------------
-- SOURCE / VERSION AUDIT
--
-- Lluis Eriksson,
-- "DLR-Uniform Log-Sobolev Inequality and Unconditional Mass Gap for
-- Lattice Yang--Mills at Weak Coupling", version 1, February 2026,
-- ai.viXra:2602.0053v1. No DOI assigned.
--
-- The July 2026 replacement is:
-- Lluis Eriksson,
-- "DLR-Uniform Log-Sobolev Inequality and Mass Gap for Lattice Yang--Mills
-- at Weak Coupling: a Conditional and Windowed Reduction",
-- ai.viXra:2602.0053v2. No DOI assigned.
--
-- VERSION-CRITICAL BOUNDARY
--
-- v1 states an unconditional DLR-uniform LSI / transfer-matrix gap, but its
-- own Remark 3.6 leaves the block Dobrushin condition unverified.  v2
-- explicitly withdraws the unconditional claim and retains the DLR route
-- only conditionally/windowed, with named hypotheses including H-DOB-blk and
-- H-P0.
--
-- The local v1 observation which survives the audit is useful: frozen
-- boundary links enter a fast fibre as parameters.  What does NOT follow is
-- that the resulting per-block oscillation is O(1) uniformly in beta.
-- The displayed v1 majorant itself has the form
--
--     C_fib(beta,n,c) = 2 beta n + c.
--
-- This file proves the exact beta-increment identity.  Thus whenever the
-- plaquette-count coefficient n is nonzero, beta-dependence is structural and
-- cannot be erased by calling C_fib a boundary-uniform constant.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing

open import DASHI.Physics.YangMills.CompactLieProofLevel

fibreOscillationMajorant : ℚ → ℚ → ℚ → ℚ
fibreOscillationMajorant beta plaquetteCount polymerResidual =
  (2 * beta * plaquetteCount) + polymerResidual

fibreOscillationBetaIncrementExact :
  ∀ beta delta plaquetteCount polymerResidual →
  fibreOscillationMajorant
    (beta + delta) plaquetteCount polymerResidual
  - fibreOscillationMajorant
      beta plaquetteCount polymerResidual
  ≡ 2 * delta * plaquetteCount
fibreOscillationBetaIncrementExact = ℚRing.solve-∀

fibreOscillationZeroPlaquetteBetaIndependent :
  ∀ beta delta polymerResidual →
  fibreOscillationMajorant
    (beta + delta) 0 polymerResidual
  ≡ fibreOscillationMajorant beta 0 polymerResidual
fibreOscillationZeroPlaquetteBetaIndependent = ℚRing.solve-∀

frozenBoundaryUniformityDoesNotRemoveBetaCoefficient :
  ∀ beta plaquetteCount polymerResidual →
  fibreOscillationMajorant beta plaquetteCount polymerResidual
  ≡ 2 * beta * plaquetteCount + polymerResidual
frozenBoundaryUniformityDoesNotRemoveBetaCoefficient beta plaquetteCount polymerResidual = refl

------------------------------------------------------------------------
-- Version/status carrier.  The theorem-bearing boundary is explicit rather
-- than encoded as a Boolean claim of unconditional closure.
------------------------------------------------------------------------

data Eriksson26020053Version : Set where
  februaryV1 : Eriksson26020053Version
  julyV2 : Eriksson26020053Version

data DLRMassGapStatus : Set where
  claimedUnconditional : DLRMassGapStatus
  conditionalWindowed : DLRMassGapStatus

statusOf : Eriksson26020053Version → DLRMassGapStatus
statusOf februaryV1 = claimedUnconditional
statusOf julyV2 = conditionalWindowed

julyV2StatusIsConditionalWindowed :
  statusOf julyV2 ≡ conditionalWindowed
julyV2StatusIsConditionalWindowed = refl

februaryV1UnconditionalClosureLevel : ProofLevel
februaryV1UnconditionalClosureLevel = conjectural

julyV2DLRFrontEndLevel : ProofLevel
julyV2DLRFrontEndLevel = conditional

frozenBoundaryLocalMechanismLevel : ProofLevel
frozenBoundaryLocalMechanismLevel = standardImported

fibreOscillationBetaIncrementLevel : ProofLevel
fibreOscillationBetaIncrementLevel = machineChecked
