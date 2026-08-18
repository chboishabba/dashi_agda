module DASHI.Physics.Closure.NSTriadKNB2CoherenceDangerForkRound78Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Thomas Y. Hou; Ruo Li.
-- Title: "Dynamic Depletion of Vortex Stretching and Non-Blowup of the 3-D
-- Incompressible Euler Equations".
-- DOI: 10.1007/s00332-006-0800-3.
--
-- Author: Zoran Grujic.
-- Title: "Vortex stretching and anisotropic diffusion in the 3D
-- Navier-Stokes equations".
-- DOI: 10.48550/arXiv.1405.3498.
--
-- ROUND78 / EXISTING COHERENCE FORK -> B2 KILL TEST
--
-- The repository already has an exhaustive logical middle-eigenvalue fork:
--
--   lambda2 <= 0
--   or small middle alignment
--   or a genuine middle-channel leak,
--
-- and the leak is to be resolved by coherence turnover, loss of packet
-- tightness, or viscous absorption.
--
-- Round78 does not create a parallel CFM classifier.  Instead it proves the
-- exact B2 consequence: if whichever branch occurs supplies a SAME-EVENT
-- depletion-dominance proof, then a strictly frame-weighted supercritical row
-- is impossible.  Therefore a successful B2 event must escape at least one of
-- those quantitative depletion/turnover/tail/viscous resolutions.
------------------------------------------------------------------------

open import Agda.Primitive using (Set)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSMiddleEigenvalueDangerFork as Fork
import DASHI.Physics.Closure.NSTriadKNFrameWeightedSupercriticalPropagationRound77Exact as Propagation
import DASHI.Physics.Closure.NSTriadKNFrameWeightedStretchingDepletionGateRound78Exact as Gate

record QuantitativeDangerResolution
    {row : Propagation.FrameWeightedSupercriticalRow}
    (decomposition : Gate.PhysicalExcessDecomposition row)
    (Biaxial AlignmentSmall Turnover Tail Viscous : Set) : Set where
  field
    qualitative :
      Fork.DangerousTransferResolution
        Biaxial AlignmentSmall Turnover Tail Viscous

    biaxialDominates : Biaxial →
      Gate.crossModeNonlocalEnable decomposition
      Gate.≤ Gate.pressureGeometryAndAllocationDepletion decomposition

    smallAlignmentDominates : AlignmentSmall →
      Gate.crossModeNonlocalEnable decomposition
      Gate.≤ Gate.pressureGeometryAndAllocationDepletion decomposition

    turnoverDominates : Turnover →
      Gate.crossModeNonlocalEnable decomposition
      Gate.≤ Gate.pressureGeometryAndAllocationDepletion decomposition

    lostTightnessDominates : Tail →
      Gate.crossModeNonlocalEnable decomposition
      Gate.≤ Gate.pressureGeometryAndAllocationDepletion decomposition

    viscousDominates : Viscous →
      Gate.crossModeNonlocalEnable decomposition
      Gate.≤ Gate.pressureGeometryAndAllocationDepletion decomposition

open QuantitativeDangerResolution public

resolutionGivesDominance :
  ∀ {row decomposition Biaxial AlignmentSmall Turnover Tail Viscous} →
  QuantitativeDangerResolution
    {row = row} decomposition Biaxial AlignmentSmall Turnover Tail Viscous →
  Gate.crossModeNonlocalEnable decomposition
  Gate.≤ Gate.pressureGeometryAndAllocationDepletion decomposition
resolutionGivesDominance certificate with qualitative certificate
... | Fork.biaxialDepletion proof = biaxialDominates certificate proof
... | Fork.alignmentDepletion proof = smallAlignmentDominates certificate proof
... | Fork.coherenceTurnover proof = turnoverDominates certificate proof
... | Fork.packetTightnessLost proof = lostTightnessDominates certificate proof
... | Fork.viscosityAbsorbs proof = viscousDominates certificate proof

quantitativelyResolvedDangerRefutesB2 :
  ∀ {row decomposition Biaxial AlignmentSmall Turnover Tail Viscous} →
  (certificate : QuantitativeDangerResolution
    {row = row} decomposition Biaxial AlignmentSmall Turnover Tail Viscous) →
  ⊥
quantitativelyResolvedDangerRefutesB2 {decomposition = decomposition} certificate =
  Gate.physicalSupercriticalRowRefutesDepletionDominance
    decomposition
    (resolutionGivesDominance certificate)

round78QualitativeCoherenceLabelAloneKillsB2 : Bool
round78QualitativeCoherenceLabelAloneKillsB2 = false

round78QuantitativeResolvedDangerKillsB2 : Bool
round78QuantitativeResolvedDangerKillsB2 = true

round78B2MustEscapeQuantitativeDepletionFork : Bool
round78B2MustEscapeQuantitativeDepletionFork = true

round78QuantitativeResolvedDangerKillsB2IsTrue :
  round78QuantitativeResolvedDangerKillsB2 ≡ true
round78QuantitativeResolvedDangerKillsB2IsTrue = refl
