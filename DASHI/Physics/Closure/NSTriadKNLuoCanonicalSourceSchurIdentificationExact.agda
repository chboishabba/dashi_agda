module DASHI.Physics.Closure.NSTriadKNLuoCanonicalSourceSchurIdentificationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
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
-- Make the canonical source-to-Schur choices definitionally. The weighted
-- shell energy is the mature physical bridge's cutoff-energy majorant and the
-- source energy sum is literally the low plus high source energy. Therefore
-- their two coherence equalities are reflexivity, not additional physical
-- assumptions.
--
-- The remaining leaves are exactly the nontrivial identifications: source
-- flux, source low gradient, the shell-independent Schur constant, source
-- scalar operations, and domination of the canonical source energy by the
-- mature weighted majorant.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
import Data.Rational.Base as ℚBase
open ℚBase using (ℚ)

import DASHI.Physics.Closure.NSTriadKNLuoOfficialPreBudgetDataExact as PreBudget
import DASHI.Physics.Closure.NSTriadKNLuoExactFluxKernelDecompositionExact as Source
import DASHI.Physics.Closure.NSTriadKNLuoThreePiecePhysicalSchurAdapterExact as Schur
import DASHI.Physics.Closure.NSTriadKNPhysicalCutoffFluxWeightedSchurExact as Physical

record CanonicalSourceSchurPhysicalLeaves
    {d s t : Level}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    (data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time)
    (Tensor : Set)
    (source : Source.LuoExactFluxKernelDecomposition ⊤ Tensor ℚ)
    : Setω where
  field
    commonSchurConstant : ℚ

    commonSchurConstantMatchesPhysicalBridge :
      (shell : Nat) →
      commonSchurConstant
      ≡ Physical.profileSchurConstant
          (PreBudget.preBudgetPhysicalBridge data shell)

    canonicalSourceEnergyDominatedByWeightedSchur :
      (shell : Nat) →
      Source.lessOrEqual source
        (Source.addScalar source
          (Source.lowShellEnergy source shell tt)
          (Source.highShellEnergy source shell tt))
        (Source.multiply source
          commonSchurConstant
          (Physical.cutoffEnergyMajorant
            (PreBudget.preBudgetPhysicalBridge data shell)))

    sourceAbsoluteFluxMatchesPhysicalBridge :
      (shell : Nat) →
      Source.absoluteHighFlux source shell tt
      ≡ Physical.absoluteCutoffFlux
          (PreBudget.preBudgetPhysicalBridge data shell)

    sourceLowGradientMatchesPhysicalBridge :
      (shell : Nat) →
      Source.lowGradientInfinity source shell tt
      ≡ Physical.lowPassGradientInfinity
          (PreBudget.preBudgetPhysicalBridge data shell)

    sourceMultiplyIsRationalMultiply :
      (left right : ℚ) →
      Source.multiply source left right ≡ ℚBase._*_ left right

    sourceOrderIsRationalOrder :
      (left right : ℚ) →
      Source.lessOrEqual source left right ≡ ℚBase._≤_ left right

open CanonicalSourceSchurPhysicalLeaves public

canonicalWeightedShellEnergy :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time}
    {Tensor : Set}
    {source : Source.LuoExactFluxKernelDecomposition ⊤ Tensor ℚ} →
  CanonicalSourceSchurPhysicalLeaves data Tensor source →
  Nat → ℚ
canonicalWeightedShellEnergy {data = data} leaves shell =
  Physical.cutoffEnergyMajorant
    (PreBudget.preBudgetPhysicalBridge data shell)

canonicalSourceEnergySum :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time}
    {Tensor : Set}
    {source : Source.LuoExactFluxKernelDecomposition ⊤ Tensor ℚ} →
  CanonicalSourceSchurPhysicalLeaves data Tensor source →
  Nat → ℚ
canonicalSourceEnergySum {source = source} leaves shell =
  Source.addScalar source
    (Source.lowShellEnergy source shell tt)
    (Source.highShellEnergy source shell tt)

canonicalThreePiecePhysicalSchurAdapter :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time}
    {Tensor : Set}
    {source : Source.LuoExactFluxKernelDecomposition ⊤ Tensor ℚ} →
  (leaves : CanonicalSourceSchurPhysicalLeaves data Tensor source) →
  Schur.LuoThreePiecePhysicalSchurAdapter source
canonicalThreePiecePhysicalSchurAdapter
  {data = data} {source = source} leaves = record
  { bridgeAt = λ shell state → PreBudget.preBudgetPhysicalBridge data shell
  ; commonSchurConstant = commonSchurConstant leaves
  ; weightedShellEnergy = λ shell state →
      canonicalWeightedShellEnergy leaves shell
  ; sourceEnergySum = λ shell state →
      canonicalSourceEnergySum leaves shell
  ; sourceEnergySumMeaning = λ shell state → refl
  ; weightedSchurDominatesSourceEnergy = λ shell state →
      canonicalSourceEnergyDominatedByWeightedSchur leaves shell
  ; sourceAbsoluteFluxMatchesBridge = λ shell state →
      sourceAbsoluteFluxMatchesPhysicalBridge leaves shell
  ; commonSchurConstantMatchesBridge = λ shell state →
      commonSchurConstantMatchesPhysicalBridge leaves shell
  ; weightedEnergyMatchesBridge = λ shell state → refl
  ; sourceLowGradientMatchesBridge = λ shell state →
      sourceLowGradientMatchesPhysicalBridge leaves shell
  ; sourceMultiplyIsRationalMultiply =
      sourceMultiplyIsRationalMultiply leaves
  ; sourceOrderIsRationalOrder =
      sourceOrderIsRationalOrder leaves
  }

canonicalFluxKernelToWeightedSchur :
  ∀ {d s t}
    {InitialDatum : Set d}
    {Solution : Set s}
    {Time : Set t}
    {data : PreBudget.OfficialLuoPreBudgetData
      InitialDatum Solution Time}
    {Tensor : Set}
    {source : Source.LuoExactFluxKernelDecomposition ⊤ Tensor ℚ} →
  CanonicalSourceSchurPhysicalLeaves data Tensor source →
  Source.LuoFluxKernelToWeightedSchur source
canonicalFluxKernelToWeightedSchur leaves =
  Schur.threePieceAdapterToWeightedSchur
    (canonicalThreePiecePhysicalSchurAdapter leaves)

canonicalSourceEnergyMeaningDefinitional : Bool
canonicalSourceEnergyMeaningDefinitional = true

canonicalWeightedEnergyMeaningDefinitional : Bool
canonicalWeightedEnergyMeaningDefinitional = true

canonicalSourceSchurConstructorClosed : Bool
canonicalSourceSchurConstructorClosed = true

canonicalSourceEnergyMeaningDefinitionalIsTrue :
  canonicalSourceEnergyMeaningDefinitional ≡ true
canonicalSourceEnergyMeaningDefinitionalIsTrue = refl

canonicalWeightedEnergyMeaningDefinitionalIsTrue :
  canonicalWeightedEnergyMeaningDefinitional ≡ true
canonicalWeightedEnergyMeaningDefinitionalIsTrue = refl

canonicalSourceSchurConstructorClosedIsTrue :
  canonicalSourceSchurConstructorClosed ≡ true
canonicalSourceSchurConstructorClosedIsTrue = refl
