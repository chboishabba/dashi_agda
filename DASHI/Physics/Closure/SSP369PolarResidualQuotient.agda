module DASHI.Physics.Closure.SSP369PolarResidualQuotient where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Unit using (⊤; tt)

import DASHI.Biology.TernaryCantorWheelDiffusionExact as Cantor
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ProvenanceBearingQuotient as Quotient
import DASHI.Physics.Closure.SSPPrimeLane369DepthAddressWheel as Address
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

------------------------------------------------------------------------
-- Exact reopening of the existing residual-bearing 9 -> 6 projection.
--
-- The codomain is not the six-state polar carrier alone. It is the existing
-- PolarProjectionResult = polar cell + zero-branch residual.  The residual
-- retains phase, so every full ternary phase cell is reconstructible exactly.
------------------------------------------------------------------------

reopenPolarResult : Address.PolarProjectionResult → Wheel.FullPhaseCell
reopenPolarResult (Address.projectedPolar cell) = Wheel.embedPolarPhaseCell cell
reopenPolarResult (Address.zeroBranchResidual phase) = Triadic.zeroTrit , phase

reopenPolarProjectExact :
  (cell : Wheel.FullPhaseCell) →
  reopenPolarResult (Address.polarProject cell) ≡ cell
reopenPolarProjectExact (Triadic.negativeTrit , phase) = refl
reopenPolarProjectExact (Triadic.zeroTrit , phase) = refl
reopenPolarProjectExact (Triadic.positiveTrit , phase) = refl

------------------------------------------------------------------------
-- Canonical quotient adapter. The residual is already carried in the surface,
-- so the extra receipt is Unit. This is a lossless residual-bearing projection,
-- not a fabricated direct 9 -> 6 retraction.
------------------------------------------------------------------------

polarResidualCore : Fibre.FibreRestrictionCore
polarResidualCore = Fibre.fibreRestrictionCore
  Wheel.FullPhaseCell
  Address.PolarProjectionResult
  ⊤
  Address.polarProject
  (λ surface → ⊤)
  (λ evidence surface → ⊤)
  false
  false

polarResidualQuotient :
  Quotient.ProvenanceBearingQuotient polarResidualCore
polarResidualQuotient = Quotient.provenanceBearingQuotient
  ⊤
  (λ cell → tt)
  (λ surface receipt → reopenPolarResult surface)
  reopenPolarProjectExact

polarEmbeddingProjectsWithoutResidual :
  (cell : Wheel.PolarPhaseCell) →
  Address.polarProject (Wheel.embedPolarPhaseCell cell)
  ≡ Address.projectedPolar cell
polarEmbeddingProjectsWithoutResidual = Address.polarProjectAfterEmbedding

zeroBranchKeepsDepthPhase :
  (phase : Wheel.DepthWheelPhase) →
  Address.polarProject (Triadic.zeroTrit , phase)
  ≡ Address.zeroBranchResidual phase
zeroBranchKeepsDepthPhase = Address.zeroProjectionRetainsPhase
