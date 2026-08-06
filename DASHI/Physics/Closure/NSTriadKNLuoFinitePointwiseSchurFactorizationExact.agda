module DASHI.Physics.Closure.NSTriadKNLuoFinitePointwiseSchurFactorizationExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Loukas Grafakos; Rodolfo H. Torres.
-- Title: "A Multilinear Schur Test and Multiplier Operators".
-- Journal of Functional Analysis 187 (2001), 1--24.
-- DOI: 10.1006/jfan.2001.3804.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Close the algebra between an actual factorized pair magnitude and the
-- canonical pointwise Schur hypothesis.  The pair magnitude is defined as
--
--   multiplierMagnitude(j,d) * tensorMagnitude(j,d).
--
-- The multiplier estimate is proved in the neighbouring dyadic module.  A
-- tensor-energy comparison then yields
--
--   pairMagnitude(j,d)
--     <= (1/4)^j (1/32)^d lowGradient weightedEnergy.
--
-- The existing rectangle theorem is instantiated from this derived estimate,
-- so neither the pointwise Schur inequality nor the complete sum is accepted
-- as a field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicMultiplierMagnitudeExact as Dyadic
import DASHI.Physics.Closure.NSTriadKNLuoFinitePhysicalSchurSummationExact as Schur
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo

record FiniteFactorizedInteraction : Set where
  constructor finite-factorized-interaction
  field
    multiplierProfile : Dyadic.FiniteDyadicMultiplierProfile
    tensorMagnitude : Nat → Nat → ℚ
    weightedEnergy : ℚ

    tensorMagnitudeNonnegative :
      (lowShell gap : Nat) → 0ℚ ≤ tensorMagnitude lowShell gap
    weightedEnergyNonnegative : 0ℚ ≤ weightedEnergy

    tensorMagnitudeBound :
      (lowShell gap : Nat) →
      tensorMagnitude lowShell gap ≤ weightedEnergy

open FiniteFactorizedInteraction public

pairMagnitude :
  FiniteFactorizedInteraction → Nat → Nat → ℚ
pairMagnitude interaction lowShell gap =
  Dyadic.multiplierMagnitude
    (multiplierProfile interaction) lowShell gap
  * tensorMagnitude interaction lowShell gap

pairMagnitudeNonnegative :
  (interaction : FiniteFactorizedInteraction) →
  (lowShell gap : Nat) →
  0ℚ ≤ pairMagnitude interaction lowShell gap
pairMagnitudeNonnegative interaction lowShell gap =
  let
    instance
      multiplierIsNonnegative =
        nonNegative
          (Dyadic.multiplierMagnitudeNonnegative
            (multiplierProfile interaction) lowShell gap)
      tensorIsNonnegative =
        nonNegative
          (tensorMagnitudeNonnegative interaction lowShell gap)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (Dyadic.multiplierMagnitude
            (multiplierProfile interaction) lowShell gap)
          (tensorMagnitude interaction lowShell gap)
  in
  ℚₚ.nonNegative⁻¹
    (pairMagnitude interaction lowShell gap)

pointwiseFactorizedSchur :
  (interaction : FiniteFactorizedInteraction) →
  (lowShell gap : Nat) →
  pairMagnitude interaction lowShell gap
  ≤ Majorant.canonicalKernel lowShell gap
      * ( Dyadic.lowGradient (multiplierProfile interaction)
        * weightedEnergy interaction
        )
pointwiseFactorizedSchur interaction lowShell gap =
  let
    profile = multiplierProfile interaction
    tensor = tensorMagnitude interaction lowShell gap
    kernelGradient =
      Majorant.canonicalKernel lowShell gap
      * Dyadic.lowGradient profile

    firstStep :
      pairMagnitude interaction lowShell gap
      ≤ kernelGradient * tensor
    firstStep =
      let
        instance
          tensorIsNonnegative =
            nonNegative
              (tensorMagnitudeNonnegative interaction lowShell gap)
      in
      ℚₚ.*-monoʳ-≤-nonNeg
        tensor
        (Dyadic.multiplierMagnitudeBound profile lowShell gap)

    kernelGradientNonnegative : 0ℚ ≤ kernelGradient
    kernelGradientNonnegative =
      let
        instance
          kernelIsNonnegative =
            nonNegative
              (Majorant.canonicalKernelNonnegative lowShell gap)
          gradientIsNonnegative =
            nonNegative (Dyadic.lowGradientNonnegative profile)
          productIsNonnegative =
            ℚₚ.nonNeg*nonNeg⇒nonNeg
              (Majorant.canonicalKernel lowShell gap)
              (Dyadic.lowGradient profile)
      in
      ℚₚ.nonNegative⁻¹ kernelGradient

    secondStep :
      kernelGradient * tensor
      ≤ kernelGradient * weightedEnergy interaction
    secondStep =
      let instance kernelGradientIsNonnegative =
        nonNegative kernelGradientNonnegative
      in
      ℚₚ.*-monoˡ-≤-nonNeg
        kernelGradient
        (tensorMagnitudeBound interaction lowShell gap)

    associatedTarget :
      kernelGradient * weightedEnergy interaction
      ≡ Majorant.canonicalKernel lowShell gap
          * ( Dyadic.lowGradient profile
            * weightedEnergy interaction
            )
    associatedTarget =
      solve
        ( Majorant.canonicalKernel lowShell gap
        ∷ Dyadic.lowGradient profile
        ∷ weightedEnergy interaction
        ∷ []
        )
  in
  subst
    (λ upper → pairMagnitude interaction lowShell gap ≤ upper)
    associatedTarget
    (ℚₚ.≤-trans firstStep secondStep)

factorizedPhysicalSchurData :
  FiniteFactorizedInteraction → Schur.FinitePhysicalSchurData
factorizedPhysicalSchurData interaction =
  Schur.finite-physical-schur
    (pairMagnitude interaction)
    (Dyadic.lowGradient (multiplierProfile interaction))
    (weightedEnergy interaction)
    (Dyadic.lowGradientNonnegative (multiplierProfile interaction))
    (weightedEnergyNonnegative interaction)
    (pairMagnitudeNonnegative interaction)
    (pointwiseFactorizedSchur interaction)

factorizedInteractionRectangleBound :
  (interaction : FiniteFactorizedInteraction) →
  (lowCutoff gapCutoff : Nat) →
  Majorant.rectangleSum
    (pairMagnitude interaction) lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds
      * ( Dyadic.lowGradient (multiplierProfile interaction)
        * weightedEnergy interaction
        )
factorizedInteractionRectangleBound interaction lowCutoff gapCutoff =
  Schur.finitePhysicalSchurRectangleBound
    (factorizedPhysicalSchurData interaction)
    lowCutoff
    gapCutoff

factorizedPointwiseSchurClosed : Bool
factorizedPointwiseSchurClosed = true

factorizedRectangleSchurClosed : Bool
factorizedRectangleSchurClosed = true

factorizedPointwiseSchurClosedIsTrue :
  factorizedPointwiseSchurClosed ≡ true
factorizedPointwiseSchurClosedIsTrue = refl

factorizedRectangleSchurClosedIsTrue :
  factorizedRectangleSchurClosed ≡ true
factorizedRectangleSchurClosedIsTrue = refl
