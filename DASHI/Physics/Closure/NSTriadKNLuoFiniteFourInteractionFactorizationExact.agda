module DASHI.Physics.Closure.NSTriadKNLuoFiniteFourInteractionFactorizationExact where

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
-- Derive all four finite Section-4 pointwise and summed estimates from one
-- shared dyadic multiplier profile and four tensor-energy comparisons.  The
-- four canonical pointwise Schur inequalities are not fields of this record;
-- they are produced by the factorization theorem and then consumed by the
-- existing exact 512/93 aggregation theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicMultiplierMagnitudeExact as Dyadic
import DASHI.Physics.Closure.NSTriadKNLuoFinitePointwiseSchurFactorizationExact as Factor
import DASHI.Physics.Closure.NSTriadKNLuoFiniteFourInteractionSchurBoundsExact as Four

record FiniteFourFactorizedInteractions : Set where
  constructor four-factorized-interactions
  field
    multiplierProfile : Dyadic.FiniteDyadicMultiplierProfile
    weightedEnergy : ℚ
    weightedEnergyNonnegative : 0ℚ ≤ weightedEnergy

    j11LowerTensor j11UpperTensor j12Tensor j2Tensor :
      Nat → Nat → ℚ

    j11LowerTensorNonnegative :
      ∀ lowShell gap → 0ℚ ≤ j11LowerTensor lowShell gap
    j11UpperTensorNonnegative :
      ∀ lowShell gap → 0ℚ ≤ j11UpperTensor lowShell gap
    j12TensorNonnegative :
      ∀ lowShell gap → 0ℚ ≤ j12Tensor lowShell gap
    j2TensorNonnegative :
      ∀ lowShell gap → 0ℚ ≤ j2Tensor lowShell gap

    j11LowerTensorBound :
      ∀ lowShell gap → j11LowerTensor lowShell gap ≤ weightedEnergy
    j11UpperTensorBound :
      ∀ lowShell gap → j11UpperTensor lowShell gap ≤ weightedEnergy
    j12TensorBound :
      ∀ lowShell gap → j12Tensor lowShell gap ≤ weightedEnergy
    j2TensorBound :
      ∀ lowShell gap → j2Tensor lowShell gap ≤ weightedEnergy

open FiniteFourFactorizedInteractions public

j11LowerInteraction :
  FiniteFourFactorizedInteractions → Factor.FiniteFactorizedInteraction
j11LowerInteraction data =
  Factor.finite-factorized-interaction
    (multiplierProfile data)
    (j11LowerTensor data)
    (weightedEnergy data)
    (j11LowerTensorNonnegative data)
    (weightedEnergyNonnegative data)
    (j11LowerTensorBound data)

j11UpperInteraction :
  FiniteFourFactorizedInteractions → Factor.FiniteFactorizedInteraction
j11UpperInteraction data =
  Factor.finite-factorized-interaction
    (multiplierProfile data)
    (j11UpperTensor data)
    (weightedEnergy data)
    (j11UpperTensorNonnegative data)
    (weightedEnergyNonnegative data)
    (j11UpperTensorBound data)

j12Interaction :
  FiniteFourFactorizedInteractions → Factor.FiniteFactorizedInteraction
j12Interaction data =
  Factor.finite-factorized-interaction
    (multiplierProfile data)
    (j12Tensor data)
    (weightedEnergy data)
    (j12TensorNonnegative data)
    (weightedEnergyNonnegative data)
    (j12TensorBound data)

j2Interaction :
  FiniteFourFactorizedInteractions → Factor.FiniteFactorizedInteraction
j2Interaction data =
  Factor.finite-factorized-interaction
    (multiplierProfile data)
    (j2Tensor data)
    (weightedEnergy data)
    (j2TensorNonnegative data)
    (weightedEnergyNonnegative data)
    (j2TensorBound data)

factorizedFourInteractionData :
  FiniteFourFactorizedInteractions → Four.FiniteFourInteractionData
factorizedFourInteractionData data =
  Four.finite-four-interaction
    (Factor.pairMagnitude (j11LowerInteraction data))
    (Factor.pairMagnitude (j11UpperInteraction data))
    (Factor.pairMagnitude (j12Interaction data))
    (Factor.pairMagnitude (j2Interaction data))
    (Dyadic.lowGradient (multiplierProfile data))
    (weightedEnergy data)
    (Dyadic.lowGradientNonnegative (multiplierProfile data))
    (weightedEnergyNonnegative data)
    (Factor.pairMagnitudeNonnegative (j11LowerInteraction data))
    (Factor.pairMagnitudeNonnegative (j11UpperInteraction data))
    (Factor.pairMagnitudeNonnegative (j12Interaction data))
    (Factor.pairMagnitudeNonnegative (j2Interaction data))
    (Factor.pointwiseFactorizedSchur (j11LowerInteraction data))
    (Factor.pointwiseFactorizedSchur (j11UpperInteraction data))
    (Factor.pointwiseFactorizedSchur (j12Interaction data))
    (Factor.pointwiseFactorizedSchur (j2Interaction data))

factorizedJ11LowerPointwise :
  (data : FiniteFourFactorizedInteractions) →
  ∀ lowShell gap →
  Factor.pairMagnitude (j11LowerInteraction data) lowShell gap
  ≤ Majorant.canonicalKernel lowShell gap
      * ( Dyadic.lowGradient (multiplierProfile data)
        * weightedEnergy data
        )
factorizedJ11LowerPointwise data =
  Factor.pointwiseFactorizedSchur (j11LowerInteraction data)

factorizedJ11UpperPointwise :
  (data : FiniteFourFactorizedInteractions) →
  ∀ lowShell gap →
  Factor.pairMagnitude (j11UpperInteraction data) lowShell gap
  ≤ Majorant.canonicalKernel lowShell gap
      * ( Dyadic.lowGradient (multiplierProfile data)
        * weightedEnergy data
        )
factorizedJ11UpperPointwise data =
  Factor.pointwiseFactorizedSchur (j11UpperInteraction data)

factorizedJ12Pointwise :
  (data : FiniteFourFactorizedInteractions) →
  ∀ lowShell gap →
  Factor.pairMagnitude (j12Interaction data) lowShell gap
  ≤ Majorant.canonicalKernel lowShell gap
      * ( Dyadic.lowGradient (multiplierProfile data)
        * weightedEnergy data
        )
factorizedJ12Pointwise data =
  Factor.pointwiseFactorizedSchur (j12Interaction data)

factorizedJ2Pointwise :
  (data : FiniteFourFactorizedInteractions) →
  ∀ lowShell gap →
  Factor.pairMagnitude (j2Interaction data) lowShell gap
  ≤ Majorant.canonicalKernel lowShell gap
      * ( Dyadic.lowGradient (multiplierProfile data)
        * weightedEnergy data
        )
factorizedJ2Pointwise data =
  Factor.pointwiseFactorizedSchur (j2Interaction data)

factorizedSection4TotalBound :
  (data : FiniteFourFactorizedInteractions) →
  (lowCutoff gapCutoff : Nat) →
  Four.section4TotalMagnitude
    (factorizedFourInteractionData data)
    lowCutoff
    gapCutoff
  ≤ Four.section4AggregateConstant
      * ( Dyadic.lowGradient (multiplierProfile data)
        * weightedEnergy data
        )
factorizedSection4TotalBound data lowCutoff gapCutoff =
  Four.section4TotalFiniteBound
    (factorizedFourInteractionData data)
    lowCutoff
    gapCutoff

fourPhysicalPointwiseBoundsDerivedFromFactors : Bool
fourPhysicalPointwiseBoundsDerivedFromFactors = true

fourPhysicalSummedBoundsDerivedFromFactors : Bool
fourPhysicalSummedBoundsDerivedFromFactors = true

fourPhysicalPointwiseBoundsDerivedFromFactorsIsTrue :
  fourPhysicalPointwiseBoundsDerivedFromFactors ≡ true
fourPhysicalPointwiseBoundsDerivedFromFactorsIsTrue = refl

fourPhysicalSummedBoundsDerivedFromFactorsIsTrue :
  fourPhysicalSummedBoundsDerivedFromFactors ≡ true
fourPhysicalSummedBoundsDerivedFromFactorsIsTrue = refl
