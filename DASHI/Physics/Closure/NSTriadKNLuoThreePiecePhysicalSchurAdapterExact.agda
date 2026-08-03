module DASHI.Physics.Closure.NSTriadKNLuoThreePiecePhysicalSchurAdapterExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- PURPOSE
-- Specialize Luo's exact three-piece flux decomposition to the repository's
-- rational Hermitian pair-incidence bridge.  Once the physical atom bridge is
-- identified with the source flux, energy and low-gradient quantities, the
-- Proposition-3.1 weighted-Schur estimate is derived by rewriting the already
-- proved physical theorem; it is not supplied as a fresh estimate field.
-- Source multiplication and order are identified explicitly as well: matching
-- only the four scalar values is not enough to transport an inequality.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Rational.Base as ℚBase
open ℚBase using (ℚ)

import DASHI.Physics.Closure.NSTriadKNLuoExactFluxKernelDecompositionExact as Luo
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact as Physical

record LuoThreePiecePhysicalSchurAdapter
    {stateLevel tensorLevel : Level}
    {State : Set stateLevel}
    {Tensor : Set tensorLevel}
    (source : Luo.LuoExactFluxKernelDecomposition State Tensor ℚ)
    : Set (lsuc (stateLevel ⊔ tensorLevel)) where
  field
    bridgeAt :
      Nat → State → Physical.PhysicalCutoffFluxWeightedSchurBridge

    commonSchurConstant : ℚ
    weightedShellEnergy : Nat → State → ℚ
    sourceEnergySum : Nat → State → ℚ

    sourceEnergySumMeaning :
      (shell : Nat) → (u : State) →
      sourceEnergySum shell u
      ≡ Luo.addScalar source
          (Luo.lowShellEnergy source shell u)
          (Luo.highShellEnergy source shell u)

    weightedSchurDominatesSourceEnergy :
      (shell : Nat) → (u : State) →
      Luo.lessOrEqual source
        (sourceEnergySum shell u)
        (Luo.multiply source
          commonSchurConstant
          (weightedShellEnergy shell u))

    sourceAbsoluteFluxMatchesBridge :
      (shell : Nat) → (u : State) →
      Luo.absoluteHighFlux source shell u
      ≡ Physical.absoluteCutoffFlux (bridgeAt shell u)

    commonSchurConstantMatchesBridge :
      (shell : Nat) → (u : State) →
      commonSchurConstant
      ≡ Physical.profileSchurConstant (bridgeAt shell u)

    weightedEnergyMatchesBridge :
      (shell : Nat) → (u : State) →
      weightedShellEnergy shell u
      ≡ Physical.cutoffEnergyMajorant (bridgeAt shell u)

    sourceLowGradientMatchesBridge :
      (shell : Nat) → (u : State) →
      Luo.lowGradientInfinity source shell u
      ≡ Physical.lowPassGradientInfinity (bridgeAt shell u)

    sourceMultiplyIsRationalMultiply :
      (left right : ℚ) →
      Luo.multiply source left right
      ≡ ℚBase._*_ left right

    sourceOrderIsRationalOrder :
      (left right : ℚ) →
      Luo.lessOrEqual source left right
      ≡ ℚBase._≤_ left right

open LuoThreePiecePhysicalSchurAdapter public

physicalFluxBoundFromExistingBridge :
  ∀ {stateLevel tensorLevel}
    {State : Set stateLevel}
    {Tensor : Set tensorLevel}
    {source : Luo.LuoExactFluxKernelDecomposition State Tensor ℚ} →
  (adapter : LuoThreePiecePhysicalSchurAdapter source) →
  (shell : Nat) →
  (u : State) →
  Luo.lessOrEqual source
    (Luo.absoluteHighFlux source shell u)
    (Luo.multiply source
      (Luo.multiply source
        (commonSchurConstant adapter)
        (weightedShellEnergy adapter shell u))
      (Luo.lowGradientInfinity source shell u))
physicalFluxBoundFromExistingBridge {source = source} adapter shell u
  rewrite sourceAbsoluteFluxMatchesBridge adapter shell u
        | commonSchurConstantMatchesBridge adapter shell u
        | weightedEnergyMatchesBridge adapter shell u
        | sourceLowGradientMatchesBridge adapter shell u
        | sourceMultiplyIsRationalMultiply adapter
            (Physical.profileSchurConstant (bridgeAt adapter shell u))
            (Physical.cutoffEnergyMajorant (bridgeAt adapter shell u))
        | sourceMultiplyIsRationalMultiply adapter
            (ℚBase._*_
              (Physical.profileSchurConstant (bridgeAt adapter shell u))
              (Physical.cutoffEnergyMajorant (bridgeAt adapter shell u)))
            (Physical.lowPassGradientInfinity (bridgeAt adapter shell u))
        | sourceOrderIsRationalOrder adapter
            (Physical.absoluteCutoffFlux (bridgeAt adapter shell u))
            (ℚBase._*_
              (ℚBase._*_
                (Physical.profileSchurConstant (bridgeAt adapter shell u))
                (Physical.cutoffEnergyMajorant (bridgeAt adapter shell u)))
              (Physical.lowPassGradientInfinity (bridgeAt adapter shell u))) =
  Physical.luoCutoffFluxEstimate (bridgeAt adapter shell u)

threePieceAdapterToWeightedSchur :
  ∀ {stateLevel tensorLevel}
    {State : Set stateLevel}
    {Tensor : Set tensorLevel}
    {source : Luo.LuoExactFluxKernelDecomposition State Tensor ℚ} →
  LuoThreePiecePhysicalSchurAdapter source →
  Luo.LuoFluxKernelToWeightedSchur source
threePieceAdapterToWeightedSchur adapter = record
  { weightedShellEnergy = weightedShellEnergy adapter
  ; schurConstant = commonSchurConstant adapter
  ; sourceEnergySum = sourceEnergySum adapter
  ; sourceEnergySumMeaning = sourceEnergySumMeaning adapter
  ; weightedSchurDominatesSourceEnergy =
      weightedSchurDominatesSourceEnergy adapter
  ; physicalFluxDominatedByWeightedSchur =
      physicalFluxBoundFromExistingBridge adapter
  }

luoThreePiecePhysicalSchurAdapterConstructed : Bool
luoThreePiecePhysicalSchurAdapterConstructed = true

finalFluxEstimateDerivedFromExistingBridge : Bool
finalFluxEstimateDerivedFromExistingBridge = true

canonicalThreePiecePhysicalAdapterInhabited : Bool
canonicalThreePiecePhysicalAdapterInhabited = false

luoThreePiecePhysicalSchurAdapterConstructedIsTrue :
  luoThreePiecePhysicalSchurAdapterConstructed ≡ true
luoThreePiecePhysicalSchurAdapterConstructedIsTrue = refl

finalFluxEstimateDerivedFromExistingBridgeIsTrue :
  finalFluxEstimateDerivedFromExistingBridge ≡ true
finalFluxEstimateDerivedFromExistingBridgeIsTrue = refl

canonicalThreePiecePhysicalAdapterInhabitedIsFalse :
  canonicalThreePiecePhysicalAdapterInhabited ≡ false
canonicalThreePiecePhysicalAdapterInhabitedIsFalse = refl
