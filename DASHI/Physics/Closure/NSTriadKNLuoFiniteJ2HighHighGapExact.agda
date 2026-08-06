module DASHI.Physics.Closure.NSTriadKNLuoFiniteJ2HighHighGapExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- Annales scientifiques de l'Ecole Normale Superieure 14 (1981).
-- DOI: 10.24033/asens.1404.
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
-- Specialise the Schur machinery to J2 with definitionally fixed shell
-- profiles (1/4)^j and (1/32)^d.  Only the physical tensor-energy comparison
-- remains primitive.  Pointwise domination, the complete rectangle bound,
-- and both exterior-tail estimates are derived.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ

import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicMultiplierMagnitudeExact as Dyadic
import DASHI.Physics.Closure.NSTriadKNLuoFinitePointwiseSchurFactorizationExact as Factor
import DASHI.Physics.Closure.NSTriadKNLuoFiniteSchurTailDominationExact as Tail

record FiniteJ2HighHighGapData : Set where
  field
    lowGradient weightedEnergy : ℚ
    tensorMagnitude : Nat → Nat → ℚ

    lowGradientNonnegative : 0ℚ ≤ lowGradient
    weightedEnergyNonnegative : 0ℚ ≤ weightedEnergy
    tensorMagnitudeNonnegative :
      (lowShell gap : Nat) → 0ℚ ≤ tensorMagnitude lowShell gap
    tensorMagnitudeBelowWeightedEnergy :
      (lowShell gap : Nat) →
      tensorMagnitude lowShell gap ≤ weightedEnergy

open FiniteJ2HighHighGapData public

canonicalJ2MultiplierProfile :
  FiniteJ2HighHighGapData → Dyadic.FiniteDyadicMultiplierProfile
canonicalJ2MultiplierProfile data = record
  { lowFactor = Geo.pow Geo.quarter
  ; gapFactor = Geo.pow Geo.thirtySecond
  ; lowGradient = lowGradient data
  ; lowFactorNonnegative = λ lowShell →
      Geo.powNonnegative Geo.quarter lowShell Geo.quarterNonnegative
  ; gapFactorNonnegative = λ gap →
      Geo.powNonnegative Geo.thirtySecond gap Geo.thirtySecondNonnegative
  ; lowGradientNonnegative = lowGradientNonnegative data
  ; lowFactorBound = λ lowShell → ℚₚ.≤-refl
  ; gapFactorBound = λ gap → ℚₚ.≤-refl
  }

j2FactorizedInteraction :
  FiniteJ2HighHighGapData → Factor.FiniteFactorizedInteraction
j2FactorizedInteraction data = record
  { multiplierProfile = canonicalJ2MultiplierProfile data
  ; tensorMagnitude = tensorMagnitude data
  ; weightedEnergy = weightedEnergy data
  ; tensorMagnitudeNonnegative = tensorMagnitudeNonnegative data
  ; weightedEnergyNonnegative = weightedEnergyNonnegative data
  ; tensorMagnitudeBound = tensorMagnitudeBelowWeightedEnergy data
  }

j2PairMagnitude :
  FiniteJ2HighHighGapData → Nat → Nat → ℚ
j2PairMagnitude data = Factor.pairMagnitude (j2FactorizedInteraction data)

j2PointwisePositiveKernelMajorant :
  (data : FiniteJ2HighHighGapData) →
  (lowShell gap : Nat) →
  j2PairMagnitude data lowShell gap
  ≤ Majorant.canonicalKernel lowShell gap
      * (lowGradient data * weightedEnergy data)
j2PointwisePositiveKernelMajorant data =
  Factor.pointwiseFactorizedSchur (j2FactorizedInteraction data)

j2RectangleBound :
  (data : FiniteJ2HighHighGapData) →
  (lowCutoff gapCutoff : Nat) →
  Majorant.rectangleSum
    (j2PairMagnitude data) lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds
      * (lowGradient data * weightedEnergy data)
j2RectangleBound data =
  Factor.factorizedInteractionRectangleBound
    (j2FactorizedInteraction data)

j2CommonFactorNonnegative :
  (data : FiniteJ2HighHighGapData) →
  0ℚ ≤ lowGradient data * weightedEnergy data
j2CommonFactorNonnegative data =
  let
    instance
      gradientIsNonnegative = nonNegative (lowGradientNonnegative data)
      energyIsNonnegative = nonNegative (weightedEnergyNonnegative data)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (lowGradient data) (weightedEnergy data)
  in
  ℚₚ.nonNegative⁻¹ (lowGradient data * weightedEnergy data)

j2TailData : FiniteJ2HighHighGapData → Tail.FiniteSchurTailData
j2TailData data = record
  { pairMagnitude = j2PairMagnitude data
  ; commonFactor = lowGradient data * weightedEnergy data
  ; commonFactorNonnegative = j2CommonFactorNonnegative data
  ; pointwiseTailDomination = j2PointwisePositiveKernelMajorant data
  }

j2LowExteriorTailBound :
  (data : FiniteJ2HighHighGapData) →
  (start lowTailCutoff gapCutoff : Nat) →
  Tail.lowExteriorRectangle (j2PairMagnitude data)
    start lowTailCutoff gapCutoff
  ≤ (Geo.pow Geo.quarter start
      * Geo.oneTwentyEightNinetyThirds)
      * (lowGradient data * weightedEnergy data)
j2LowExteriorTailBound data =
  Tail.finiteLowExteriorTailBound (j2TailData data)

j2GapExteriorTailBound :
  (data : FiniteJ2HighHighGapData) →
  (start gapTailCutoff lowCutoff : Nat) →
  Tail.gapExteriorRectangle (j2PairMagnitude data)
    start gapTailCutoff lowCutoff
  ≤ (Geo.pow Geo.thirtySecond start
      * Geo.oneTwentyEightNinetyThirds)
      * (lowGradient data * weightedEnergy data)
j2GapExteriorTailBound data =
  Tail.finiteGapExteriorTailBound (j2TailData data)
