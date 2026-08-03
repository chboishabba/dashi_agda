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
-- than rebuilding its finite pair-incidence summation.  `AbsorptionArithmetic`
-- intentionally owns only addition and order, so the source-specific product
-- used for Schur constant times energy times low-pass gradient is an explicit
-- field of this adapter rather than an invented projection of that arithmetic.
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
    luoProduct :
      Scalar (Closure.arithmetic program) →
      Scalar (Closure.arithmetic program) →
      Scalar (Closure.arithmetic program)

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
        (luoProduct
          profileSchurConstant
          (luoProduct cutoffEnergyMajorant lowPassGradientInfinity))

open LuoFullShellFluxAdapter public

luoFullShellCutoffFluxEstimate :
  (program : Closure.CompactGammaAnalyticClosure) →
  (K N : Nat) →
  (adapter : LuoFullShellFluxAdapter program K N) →
  _≤_ (Closure.arithmetic program)
    (absoluteCutoffFlux adapter)
    (luoProduct adapter
      (profileSchurConstant adapter)
      (luoProduct adapter
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
