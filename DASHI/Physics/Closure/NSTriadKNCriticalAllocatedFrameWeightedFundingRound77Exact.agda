module DASHI.Physics.Closure.NSTriadKNCriticalAllocatedFrameWeightedFundingRound77Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Terence Tao.
-- Title: "Quantitative bounds for critically bounded solutions to the
-- Navier-Stokes equations".
-- DOI: 10.1090/PSPUM/104/01874.
--
-- Authors: Tobias Barker; Christophe Prange.
-- Title: "Quantitative Regularity for the Navier-Stokes Equations Via
-- Spatial Concentration".
-- DOI: 10.1007/s00220-021-04122-x.
--
-- Author: Ole Christensen.
-- Title: "An Introduction to Frames and Riesz Bases".
-- DOI: 10.1007/978-3-319-25613-9.
--
-- ROUND77 / SOURCE-NATIVE ALLOCATED CRITICAL FUNDING
--
-- `ChargeAllocatedOverlay` rescales the left/right factors on the SAME Round62
-- structured atom list, preserving every triadic product exactly.  Therefore
-- its left squared mass is not an independently chosen scalar receipt: it is
-- the charge of the source-native allocated factorization itself.
--
-- A positive critical event supplies the original same-object overlay, a charge
-- allocation on that overlay, a frame bound for the allocated overlay, and the
-- same critical-ratio remainder identity.  Its allocated overlay charge is then
-- DEFINITIONALLY the event charge.  Round77 derives positive frame product,
-- constructs the reciprocal, and obtains
--
--      rho_e mu_e^2 <= Q_alloc,e.
--
-- The old C3 equality between canonical Q and a separately declared physical
-- scalar is therefore unnecessary on this route.  The remaining global physical
-- obligation is a primitive-source subpartition across the selected event
-- family, so total allocated charge fits the actual primitive budget.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational using (ℚ; Positive; _*_; _+_; _≤_)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNFactorizedEffectiveComplexityCauchyRound72Exact as Effective
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact as Structured
import DASHI.Physics.Closure.NSTriadKNStructuredTriadicFactorizationOverlayRound72Exact as Overlay
import DASHI.Physics.Closure.NSTriadKNCriticalAmplificationForcesRemainderRound69Exact as Amplification
import DASHI.Physics.Closure.NSTriadKNCriticalRatioNormalizationRound63Exact as C1
import DASHI.Physics.Closure.NSTriadKNCriticalRemainderTriadicCauchyRound71Exact as R71
import DASHI.Physics.Closure.NSTriadKNChargeAllocatedFactorizationRound77Exact as Allocation
import DASHI.Physics.Closure.NSTriadKNCriticalFrameWeightedPhysicalFundingRound77Exact as Weighted
import DASHI.Physics.Closure.NSTriadKNFrameWeightedFinalAntichainBudgetRound77Exact as Final

record AllocatedCriticalAmplificationWitness
    {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    (step : Amplification.CriticalRatioStepDecomposition positiveBlock)
    (n : Nat) (mu : ℚ)
    (atoms : List Structured.LocalizedPDEAtom)
    (sourceOverlay : Overlay.TriadicFactorizationOverlay atoms) : Set where
  field
    allocation : Allocation.ChargeAllocatedOverlay sourceOverlay
    frameProduct : ℚ
    frameBounded :
      Weighted.FrameBoundedCriticalOverlay
        (Allocation.allocateOverlay allocation) frameProduct

    amplificationPositive : Positive mu
    criticalExcess :
      Amplification.inherited step n + mu
      ≤ C1.normalizedCriticalRatio positiveBlock (suc n)
    remainderExact :
      Amplification.remainder step n ≡ R71.triadicSignedSum atoms

open AllocatedCriticalAmplificationWitness public

allocatedPhysicalWitness :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {step : Amplification.CriticalRatioStepDecomposition positiveBlock}
    {n mu atoms sourceOverlay} →
  (witness : AllocatedCriticalAmplificationWitness
    step n mu atoms sourceOverlay) →
  Weighted.PhysicalFrameWeightedAmplificationWitness
    step n mu atoms (Allocation.allocateOverlay (allocation witness))
allocatedPhysicalWitness witness = record
  { frameProduct = frameProduct witness
  ; frameBounded = frameBounded witness
  ; amplificationPositive = amplificationPositive witness
  ; criticalExcess = criticalExcess witness
  ; remainderExact = remainderExact witness
  ; physicalCharge =
      Overlay.overlayCharge (Allocation.allocateOverlay (allocation witness))
  ; physicalChargeNonnegative =
      Effective.concentrationChargeNonnegative
        (Overlay.overlayFactors (Allocation.allocateOverlay (allocation witness)))
  ; overlayChargeIsPhysicalCharge = refl
  }

allocatedReciprocalWeight :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {step : Amplification.CriticalRatioStepDecomposition positiveBlock}
    {n mu atoms sourceOverlay} →
  AllocatedCriticalAmplificationWitness step n mu atoms sourceOverlay → ℚ
allocatedReciprocalWeight witness =
  Weighted.reciprocalWeight (allocatedPhysicalWitness witness)

allocatedCriticalFloorBelowAllocatedCharge :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {step : Amplification.CriticalRatioStepDecomposition positiveBlock}
    {n mu atoms sourceOverlay} →
  (witness : AllocatedCriticalAmplificationWitness
    step n mu atoms sourceOverlay) →
  allocatedReciprocalWeight witness * L2.square mu
  ≤ Overlay.overlayCharge (Allocation.allocateOverlay (allocation witness))
allocatedCriticalFloorBelowAllocatedCharge witness =
  Weighted.frameWeightedCriticalFloorBelowPhysicalCharge
    (allocatedPhysicalWitness witness)

allocatedCriticalAsFinalFundedNode :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    {step : Amplification.CriticalRatioStepDecomposition positiveBlock}
    {n mu atoms sourceOverlay} →
  (witness : AllocatedCriticalAmplificationWitness
    step n mu atoms sourceOverlay) →
  Final.FrameWeightedFundedNode
allocatedCriticalAsFinalFundedNode witness =
  Weighted.asFinalWeightedFundedNode (allocatedPhysicalWitness witness)

round77AllocatedEventChargeIsSourceNativeByConstruction : Bool
round77AllocatedEventChargeIsSourceNativeByConstruction = true

round77SeparateCanonicalQPhysicalChargeIdentityRequired : Bool
round77SeparateCanonicalQPhysicalChargeIdentityRequired = false

round77AllocatedPositiveCriticalFundingConstructed : Bool
round77AllocatedPositiveCriticalFundingConstructed = true

round77GlobalPhysicalPrimitiveChargeSubpartitionConstructed : Bool
round77GlobalPhysicalPrimitiveChargeSubpartitionConstructed = false

round77SelectedTrajectoryProducesAllocatedCriticalWitnesses : Bool
round77SelectedTrajectoryProducesAllocatedCriticalWitnesses = false
