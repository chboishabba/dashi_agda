module DASHI.Physics.Closure.NSTriadKNLuoFullShellFluxAdapterExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal/year: Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Reuse the mature compact-Gamma/full-shell weighted-Schur development rather
-- than rebuilding its finite pair-incidence summation.  For a shared
-- `CompactGammaAnalyticClosure`, the repository already proves that the exact
-- near response is bounded by the full-shell majorant action.  Once the Luo
-- cutoff flux is identified below that near response and the majorant action
-- is factored into a cutoff-energy expression times the low-pass gradient,
-- Luo's Proposition-3.1-shaped estimate follows by transitivity.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSCompactGammaAnalyticClosureProgram as Closure
import DASHI.Physics.Closure.NSCompactGammaDifferentiatedTriadInstantiation as Triads

record LuoFullShellFluxAdapter
    (program : Closure.CompactGammaAnalyticClosure)
    (K N : Nat) : Setω where
  field
    absoluteCutoffFlux : Scalar (Closure.arithmetic program)
    cutoffEnergyMajorant : Scalar (Closure.arithmetic program)
    lowPassGradientInfinity : Scalar (Closure.arithmetic program)
    profileSchurConstant : Scalar (Closure.arithmetic program)

    absoluteCutoffFluxBelowNearResponse :
      _≤_ (Closure.arithmetic program)
        absoluteCutoffFlux
        (Triads.concreteNearResponse
          (Closure.differentiatedTriadsAt program K N))

    fullShellMajorantFactorsAsLuoProduct :
      _≤_ (Closure.arithmetic program)
        (Triads.majorantActionOutput
          (Closure.differentiatedTriadsAt program K N))
        (_*_ (Closure.arithmetic program)
          profileSchurConstant
          (_*_ (Closure.arithmetic program)
            cutoffEnergyMajorant
            lowPassGradientInfinity))

open LuoFullShellFluxAdapter public

luoFullShellCutoffFluxEstimate :
  (program : Closure.CompactGammaAnalyticClosure) →
  (K N : Nat) →
  (adapter : LuoFullShellFluxAdapter program K N) →
  _≤_ (Closure.arithmetic program)
    (absoluteCutoffFlux adapter)
    (_*_ (Closure.arithmetic program)
      (profileSchurConstant adapter)
      (_*_ (Closure.arithmetic program)
        (cutoffEnergyMajorant adapter)
        (lowPassGradientInfinity adapter)))
luoFullShellCutoffFluxEstimate program K N adapter =
  ≤-trans (Closure.arithmetic program)
    (absoluteCutoffFluxBelowNearResponse adapter)
    (≤-trans (Closure.arithmetic program)
      (Closure.closureNearResponseMajorized program K N)
      (fullShellMajorantFactorsAsLuoProduct adapter))

record LuoFullShellPhysicalIdentification
    (program : Closure.CompactGammaAnalyticClosure)
    (K N : Nat) : Setω where
  field
    adapter : LuoFullShellFluxAdapter program K N

    SelectedPairListIsHardHighPhysicalTriadImage : Set
    selectedPairListIsHardHighPhysicalTriadImage :
      SelectedPairListIsHardHighPhysicalTriadImage

    NearResponseIsLuoProjectedCutoffFlux : Set
    nearResponseIsLuoProjectedCutoffFlux :
      NearResponseIsLuoProjectedCutoffFlux

    MajorantEnergyIsLuoWeightedShellEnergy : Set
    majorantEnergyIsLuoWeightedShellEnergy :
      MajorantEnergyIsLuoWeightedShellEnergy

    LowPassGradientIsPhysicalInfinityNorm : Set
    lowPassGradientIsPhysicalInfinityNorm :
      LowPassGradientIsPhysicalInfinityNorm

    ProfileSchurConstantUniformInCutoff : Set
    profileSchurConstantUniformInCutoff :
      ProfileSchurConstantUniformInCutoff

open LuoFullShellPhysicalIdentification public

matureFullShellNearMajorizationReused : Bool
matureFullShellNearMajorizationReused = true

matureFullShellUniformSchurReused : Bool
matureFullShellUniformSchurReused = true

luoFullShellFluxCompositionConstructed : Bool
luoFullShellFluxCompositionConstructed = true

luoFullShellPhysicalIdentificationInhabited : Bool
luoFullShellPhysicalIdentificationInhabited = false

matureFullShellNearMajorizationReusedIsTrue :
  matureFullShellNearMajorizationReused ≡ true
matureFullShellNearMajorizationReusedIsTrue = refl

matureFullShellUniformSchurReusedIsTrue :
  matureFullShellUniformSchurReused ≡ true
matureFullShellUniformSchurReusedIsTrue = refl

luoFullShellFluxCompositionConstructedIsTrue :
  luoFullShellFluxCompositionConstructed ≡ true
luoFullShellFluxCompositionConstructedIsTrue = refl

luoFullShellPhysicalIdentificationInhabitedIsFalse :
  luoFullShellPhysicalIdentificationInhabited ≡ false
luoFullShellPhysicalIdentificationInhabitedIsFalse = refl
