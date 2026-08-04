module DASHI.Physics.Closure.NSTriadKNLuoFiniteFourInteractionSquaredConvolutionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Result: finite squared Cauchy--Schwarz inequality.
-- DOI: not applicable to the classical inequality.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Loukas Grafakos; Seungly Oh.
-- Title: "The Kato-Ponce Inequality".
-- Communications in Partial Differential Equations 39 (2014), 1128--1157.
-- DOI: 10.1080/03605302.2013.822885.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Apply the repository's exact restricted-fibre Cauchy--Schwarz theorem to
-- the four Luo Section-4 interaction families and prove the aggregate squared
-- estimate.  Each family owns a literal list of resonant output fibres and a
-- shell-cardinality collapse.  The four whole-family inequalities and their
-- common-cardinality aggregate are derived, not supplied as fields.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalDirectConvolutionBound as Direct

record FiniteFourSquaredConvolutionData : Set where
  constructor four-squared-convolution
  field
    fullLeftNorm fullRightNorm multiplierBoundSquared : ℚ
    fullLeftNonnegative : 0ℚ ≤ fullLeftNorm
    fullRightNonnegative : 0ℚ ≤ fullRightNorm
    multiplierBoundNonnegative : 0ℚ ≤ multiplierBoundSquared

    j11LowerOutputs j11UpperOutputs j12Outputs j2Outputs :
      List (Direct.OutputFibre
        fullLeftNorm fullRightNorm multiplierBoundSquared)

    j11LowerCardinality :
      Direct.ShellCardinalityMajorant j11LowerOutputs
    j11UpperCardinality :
      Direct.ShellCardinalityMajorant j11UpperOutputs
    j12Cardinality :
      Direct.ShellCardinalityMajorant j12Outputs
    j2Cardinality :
      Direct.ShellCardinalityMajorant j2Outputs

    commonCardinalityFactor : ℚ
    commonCardinalityNonnegative : 0ℚ ≤ commonCardinalityFactor

    j11LowerCardinalityBound :
      Direct.shellCardinalityFactor j11LowerCardinality
      ≤ commonCardinalityFactor
    j11UpperCardinalityBound :
      Direct.shellCardinalityFactor j11UpperCardinality
      ≤ commonCardinalityFactor
    j12CardinalityBound :
      Direct.shellCardinalityFactor j12Cardinality
      ≤ commonCardinalityFactor
    j2CardinalityBound :
      Direct.shellCardinalityFactor j2Cardinality
      ≤ commonCardinalityFactor

open FiniteFourSquaredConvolutionData public

commonEnergyProduct : FiniteFourSquaredConvolutionData → ℚ
commonEnergyProduct data =
  multiplierBoundSquared data
  * (fullLeftNorm data * fullRightNorm data)

commonEnergyProductNonnegative :
  (data : FiniteFourSquaredConvolutionData) →
  0ℚ ≤ commonEnergyProduct data
commonEnergyProductNonnegative data =
  let
    instance
      leftIsNonnegative = nonNegative (fullLeftNonnegative data)
      rightIsNonnegative = nonNegative (fullRightNonnegative data)
      normProductIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (fullLeftNorm data) (fullRightNorm data)
      multiplierIsNonnegative =
        nonNegative (multiplierBoundNonnegative data)
      totalIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (multiplierBoundSquared data)
          (fullLeftNorm data * fullRightNorm data)
  in
  ℚₚ.nonNegative⁻¹ (commonEnergyProduct data)

j11LowerSquaredBound :
  (data : FiniteFourSquaredConvolutionData) →
  Direct.sumOutputFibreSquares (j11LowerOutputs data)
  ≤ Direct.shellCardinalityFactor (j11LowerCardinality data)
      * commonEnergyProduct data
j11LowerSquaredBound data =
  Direct.finiteLowOutputShellBoundSquared
    (j11LowerCardinality data)

j11UpperSquaredBound :
  (data : FiniteFourSquaredConvolutionData) →
  Direct.sumOutputFibreSquares (j11UpperOutputs data)
  ≤ Direct.shellCardinalityFactor (j11UpperCardinality data)
      * commonEnergyProduct data
j11UpperSquaredBound data =
  Direct.finiteLowOutputShellBoundSquared
    (j11UpperCardinality data)

j12SquaredBound :
  (data : FiniteFourSquaredConvolutionData) →
  Direct.sumOutputFibreSquares (j12Outputs data)
  ≤ Direct.shellCardinalityFactor (j12Cardinality data)
      * commonEnergyProduct data
j12SquaredBound data =
  Direct.finiteLowOutputShellBoundSquared
    (j12Cardinality data)

j2SquaredBound :
  (data : FiniteFourSquaredConvolutionData) →
  Direct.sumOutputFibreSquares (j2Outputs data)
  ≤ Direct.shellCardinalityFactor (j2Cardinality data)
      * commonEnergyProduct data
j2SquaredBound data =
  Direct.finiteLowOutputShellBoundSquared
    (j2Cardinality data)

cardinalityTimesEnergyMonotone :
  (data : FiniteFourSquaredConvolutionData) →
  ∀ {cardinality} →
  cardinality ≤ commonCardinalityFactor data →
  cardinality * commonEnergyProduct data
  ≤ commonCardinalityFactor data * commonEnergyProduct data
cardinalityTimesEnergyMonotone data cardinalityBound =
  let instance energyIsNonnegative =
    nonNegative (commonEnergyProductNonnegative data)
  in
  ℚₚ.*-monoʳ-≤-nonNeg
    (commonEnergyProduct data)
    cardinalityBound

j11LowerCommonSquaredBound :
  (data : FiniteFourSquaredConvolutionData) →
  Direct.sumOutputFibreSquares (j11LowerOutputs data)
  ≤ commonCardinalityFactor data * commonEnergyProduct data
j11LowerCommonSquaredBound data =
  ℚₚ.≤-trans
    (j11LowerSquaredBound data)
    (cardinalityTimesEnergyMonotone data
      (j11LowerCardinalityBound data))

j11UpperCommonSquaredBound :
  (data : FiniteFourSquaredConvolutionData) →
  Direct.sumOutputFibreSquares (j11UpperOutputs data)
  ≤ commonCardinalityFactor data * commonEnergyProduct data
j11UpperCommonSquaredBound data =
  ℚₚ.≤-trans
    (j11UpperSquaredBound data)
    (cardinalityTimesEnergyMonotone data
      (j11UpperCardinalityBound data))

j12CommonSquaredBound :
  (data : FiniteFourSquaredConvolutionData) →
  Direct.sumOutputFibreSquares (j12Outputs data)
  ≤ commonCardinalityFactor data * commonEnergyProduct data
j12CommonSquaredBound data =
  ℚₚ.≤-trans
    (j12SquaredBound data)
    (cardinalityTimesEnergyMonotone data
      (j12CardinalityBound data))

j2CommonSquaredBound :
  (data : FiniteFourSquaredConvolutionData) →
  Direct.sumOutputFibreSquares (j2Outputs data)
  ≤ commonCardinalityFactor data * commonEnergyProduct data
j2CommonSquaredBound data =
  ℚₚ.≤-trans
    (j2SquaredBound data)
    (cardinalityTimesEnergyMonotone data
      (j2CardinalityBound data))

totalSquaredInteraction : FiniteFourSquaredConvolutionData → ℚ
totalSquaredInteraction data =
  Direct.sumOutputFibreSquares (j11LowerOutputs data)
  + Direct.sumOutputFibreSquares (j11UpperOutputs data)
  + Direct.sumOutputFibreSquares (j12Outputs data)
  + Direct.sumOutputFibreSquares (j2Outputs data)

fourTimesCommonSquaredMajorant : FiniteFourSquaredConvolutionData → ℚ
fourTimesCommonSquaredMajorant data =
  (commonCardinalityFactor data * commonEnergyProduct data)
  + (commonCardinalityFactor data * commonEnergyProduct data)
  + (commonCardinalityFactor data * commonEnergyProduct data)
  + (commonCardinalityFactor data * commonEnergyProduct data)

totalSquaredInteractionBound :
  (data : FiniteFourSquaredConvolutionData) →
  totalSquaredInteraction data
  ≤ fourTimesCommonSquaredMajorant data
totalSquaredInteractionBound data =
  ℚₚ.+-mono-≤
    (ℚₚ.+-mono-≤
      (ℚₚ.+-mono-≤
        (j11LowerCommonSquaredBound data)
        (j11UpperCommonSquaredBound data))
      (j12CommonSquaredBound data))
    (j2CommonSquaredBound data)

fourTimesCommonSquaredMajorantFactorized :
  (data : FiniteFourSquaredConvolutionData) →
  fourTimesCommonSquaredMajorant data
  ≡ (commonCardinalityFactor data
      + commonCardinalityFactor data
      + commonCardinalityFactor data
      + commonCardinalityFactor data)
      * commonEnergyProduct data
fourTimesCommonSquaredMajorantFactorized data =
  solve
    ( commonCardinalityFactor data
    ∷ commonEnergyProduct data
    ∷ []
    )

finiteFourInteractionSquaredConvolutionClosed : Bool
finiteFourInteractionSquaredConvolutionClosed = true

finiteFourInteractionCommonCardinalityClosed : Bool
finiteFourInteractionCommonCardinalityClosed = true

finiteFourInteractionSquaredConvolutionClosedIsTrue :
  finiteFourInteractionSquaredConvolutionClosed ≡ true
finiteFourInteractionSquaredConvolutionClosedIsTrue = refl

finiteFourInteractionCommonCardinalityClosedIsTrue :
  finiteFourInteractionCommonCardinalityClosed ≡ true
finiteFourInteractionCommonCardinalityClosedIsTrue = refl
