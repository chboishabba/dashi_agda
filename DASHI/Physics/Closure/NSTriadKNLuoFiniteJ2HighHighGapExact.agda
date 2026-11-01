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
canonicalJ2MultiplierProfile gapData = record
  { lowFactor = Geo.pow Geo.quarter
  ; gapFactor = Geo.pow Geo.thirtySecond
  ; lowGradient = lowGradient gapData
  ; lowFactorNonnegative = λ lowShell →
      Geo.powNonnegative Geo.quarter lowShell Geo.quarterNonnegative
  ; gapFactorNonnegative = λ gap →
      Geo.powNonnegative Geo.thirtySecond gap Geo.thirtySecondNonnegative
  ; lowGradientNonnegative = lowGradientNonnegative gapData
  ; lowFactorBound = λ lowShell → ℚₚ.≤-refl
  ; gapFactorBound = λ gap → ℚₚ.≤-refl
  }

j2FactorizedInteraction :
  FiniteJ2HighHighGapData → Factor.FiniteFactorizedInteraction
j2FactorizedInteraction gapData = record
  { multiplierProfile = canonicalJ2MultiplierProfile gapData
  ; tensorMagnitude = tensorMagnitude gapData
  ; weightedEnergy = weightedEnergy gapData
  ; tensorMagnitudeNonnegative = tensorMagnitudeNonnegative gapData
  ; weightedEnergyNonnegative = weightedEnergyNonnegative gapData
  ; tensorMagnitudeBound = tensorMagnitudeBelowWeightedEnergy gapData
  }

j2PairMagnitude :
  FiniteJ2HighHighGapData → Nat → Nat → ℚ
j2PairMagnitude gapData = Factor.pairMagnitude (j2FactorizedInteraction gapData)

j2PointwisePositiveKernelMajorant :
  (gapData : FiniteJ2HighHighGapData) →
  (lowShell gap : Nat) →
  j2PairMagnitude gapData lowShell gap
  ≤ Majorant.canonicalKernel lowShell gap
      * (lowGradient gapData * weightedEnergy gapData)
j2PointwisePositiveKernelMajorant gapData =
  Factor.pointwiseFactorizedSchur (j2FactorizedInteraction gapData)

j2RectangleBound :
  (gapData : FiniteJ2HighHighGapData) →
  (lowCutoff gapCutoff : Nat) →
  Majorant.rectangleSum
    (j2PairMagnitude gapData) lowCutoff gapCutoff
  ≤ Geo.oneTwentyEightNinetyThirds
      * (lowGradient gapData * weightedEnergy gapData)
j2RectangleBound gapData =
  Factor.factorizedInteractionRectangleBound
    (j2FactorizedInteraction gapData)

j2CommonFactorNonnegative :
  (gapData : FiniteJ2HighHighGapData) →
  0ℚ ≤ lowGradient gapData * weightedEnergy gapData
j2CommonFactorNonnegative gapData =
  let
    instance
      gradientIsNonnegative = nonNegative (lowGradientNonnegative gapData)
      energyIsNonnegative = nonNegative (weightedEnergyNonnegative gapData)
      productIsNonnegative =
        ℚₚ.nonNeg*nonNeg⇒nonNeg
          (lowGradient gapData) (weightedEnergy gapData)
  in
  ℚₚ.nonNegative⁻¹ (lowGradient gapData * weightedEnergy gapData)

j2TailData : FiniteJ2HighHighGapData → Tail.FiniteSchurTailData
j2TailData gapData = record
  { pairMagnitude = j2PairMagnitude gapData
  ; commonFactor = lowGradient gapData * weightedEnergy gapData
  ; commonFactorNonnegative = j2CommonFactorNonnegative gapData
  ; pointwiseTailDomination = j2PointwisePositiveKernelMajorant gapData
  }

j2LowExteriorTailBound :
  (gapData : FiniteJ2HighHighGapData) →
  (start lowTailCutoff gapCutoff : Nat) →
  Tail.lowExteriorRectangle (j2PairMagnitude gapData)
    start lowTailCutoff gapCutoff
  ≤ (Geo.pow Geo.quarter start
      * Geo.oneTwentyEightNinetyThirds)
      * (lowGradient gapData * weightedEnergy gapData)
j2LowExteriorTailBound gapData =
  Tail.finiteLowExteriorTailBound (j2TailData gapData)

j2GapExteriorTailBound :
  (gapData : FiniteJ2HighHighGapData) →
  (start gapTailCutoff lowCutoff : Nat) →
  Tail.gapExteriorRectangle (j2PairMagnitude gapData)
    start gapTailCutoff lowCutoff
  ≤ (Geo.pow Geo.thirtySecond start
      * Geo.oneTwentyEightNinetyThirds)
      * (lowGradient gapData * weightedEnergy gapData)
j2GapExteriorTailBound gapData =
  Tail.finiteGapExteriorTailBound (j2TailData gapData)
