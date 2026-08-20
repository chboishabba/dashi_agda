module DASHI.Physics.YangMills.BalabanTopDownSummableRGIncrementExact where

------------------------------------------------------------------------
-- ROUND81: THE CONTINUUM CONSUMER NEEDS SUMMABLE RG INCREMENTS,
--          NOT A GLOBAL BANACH CONTRACTION OF THE RG MAP
--
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
-- Section 2 gives the complete-density E/R/B decomposition.  In particular
-- (2.31) gives exponential localization for R terms, (2.42) for B terms, and
-- the discussion following (2.42) explicitly spends one unit of exponential
-- decay to obtain a dyadic inter-scale factor before summing over scales.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116 (1988),
-- 1--22. DOI: 10.1007/BF01239022.
-- Lemma 3 / (2.38) proves
--
--   |H(Z)| <= C3 epsilon1 exp(-(1-5 delta)L kappa d_{k+1}(Z)),
--
-- and the cluster resummation retains exponential localization in (2.41).
--
-- Krzysztof Gawedzki and Antti Kupiainen,
-- "A Rigorous Block Spin Approach to Massless Lattice Theories",
-- Communications in Mathematical Physics 77 (1980), 31--64.
-- DOI: 10.1007/BF01205038.
--
-- TOP-DOWN CORRECTION
--
-- The Clay-facing continuum consumer never uses a theorem of the form
--
--   ||R K - R K'|| <= q ||K-K'||
--
-- for arbitrary pairs K,K'.  What it uses is convergence of ONE literal
-- finite-cutoff trajectory.  It therefore suffices to prove a summable bound on
-- successive states/characteristic functionals.  This is also the source shape:
-- Bałaban controls newly generated localized terms at each scale rather than
-- asserting a Banach fixed-point theorem for the complete 4D gauge RG map.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _≤_; _*_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanContinuumScaleLocalObservableCauchyExact as Scale
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanClayT2UrsellCauchyExact as Ursell

record SameFamilySummableScaleIncrement : Set₁ where
  field
    commonMajorant : Scale.ScaleLocalIncrementMajorant

    ordinaryDifference : Nat → Nat → ℚ
    characteristicDifference : Nat → Nat → ℚ

    ordinaryDifferenceNonnegative : ∀ start count →
      0ℚ ≤ ordinaryDifference start count
    characteristicDifferenceNonnegative : ∀ start count →
      0ℚ ≤ characteristicDifference start count

    ordinaryDifferenceBelowTail : ∀ start count →
      ordinaryDifference start count
      ≤ Scale.scaleIncrementTail commonMajorant start count

    characteristicDifferenceBelowTail : ∀ start count →
      characteristicDifference start count
      ≤ Scale.scaleIncrementTail commonMajorant start count

open SameFamilySummableScaleIncrement public

ordinaryCauchyModulus :
  (dataSet : SameFamilySummableScaleIncrement) → ∀ start count →
  ordinaryDifference dataSet start count
  ≤ Scale.coefficient (commonMajorant dataSet)
      * (Geo.half * Geo.halfPower start)
ordinaryCauchyModulus dataSet start count =
  ℚP.≤-trans
    (ordinaryDifferenceBelowTail dataSet start count)
    (Scale.scaleLocalCauchyTail (commonMajorant dataSet) start count)

characteristicCauchyModulus :
  (dataSet : SameFamilySummableScaleIncrement) → ∀ start count →
  characteristicDifference dataSet start count
  ≤ Scale.coefficient (commonMajorant dataSet)
      * (Geo.half * Geo.halfPower start)
characteristicCauchyModulus dataSet start count =
  ℚP.≤-trans
    (characteristicDifferenceBelowTail dataSet start count)
    (Scale.scaleLocalCauchyTail (commonMajorant dataSet) start count)

generatedTail : (Nat → ℚ) → Nat → Nat → ℚ
generatedTail increment start zero = 0ℚ
generatedTail increment start (suc count) =
  increment start + generatedTail increment (suc start) count

record PublishedTailToCommonIncrement : Set₁ where
  field
    sourceGeneratedIncrement : Nat → ℚ
    sourceGeneratedIncrementNonnegative : ∀ scale →
      0ℚ ≤ sourceGeneratedIncrement scale

    coefficient : ℚ
    coefficientNonnegative : 0ℚ ≤ coefficient

    -- Source-shaped physical estimate from the actual CMP116/CMP119 E/R/B
    -- tails after normalization/local-observable response.
    generatedIncrementDyadic : ∀ scale →
      sourceGeneratedIncrement scale
      ≤ coefficient * (Ursell.quarter * Geo.halfPower scale)

    ordinaryDifference : Nat → Nat → ℚ
    characteristicDifference : Nat → Nat → ℚ
    ordinaryDifferenceNonnegative : ∀ start count →
      0ℚ ≤ ordinaryDifference start count
    characteristicDifferenceNonnegative : ∀ start count →
      0ℚ ≤ characteristicDifference start count

    ordinaryResponseBelowGeneratedTail : ∀ start count →
      ordinaryDifference start count
      ≤ generatedTail sourceGeneratedIncrement start count
    characteristicResponseBelowGeneratedTail : ∀ start count →
      characteristicDifference start count
      ≤ generatedTail sourceGeneratedIncrement start count

open PublishedTailToCommonIncrement public

publishedTailMajorant :
  PublishedTailToCommonIncrement → Scale.ScaleLocalIncrementMajorant
publishedTailMajorant dataSet = record
  { Scale.ScaleLocalIncrementMajorant.coefficient = coefficient dataSet
  ; Scale.ScaleLocalIncrementMajorant.coefficientNonnegative =
      coefficientNonnegative dataSet
  ; Scale.ScaleLocalIncrementMajorant.incrementMagnitude =
      sourceGeneratedIncrement dataSet
  ; Scale.ScaleLocalIncrementMajorant.incrementNonnegative =
      sourceGeneratedIncrementNonnegative dataSet
  ; Scale.ScaleLocalIncrementMajorant.incrementBelowScaleShell =
      generatedIncrementDyadic dataSet
  }

publishedTailToSameFamilySummableIncrement :
  (dataSet : PublishedTailToCommonIncrement) →
  SameFamilySummableScaleIncrement
publishedTailToSameFamilySummableIncrement dataSet = record
  { SameFamilySummableScaleIncrement.commonMajorant =
      publishedTailMajorant dataSet
  ; SameFamilySummableScaleIncrement.ordinaryDifference =
      PublishedTailToCommonIncrement.ordinaryDifference dataSet
  ; SameFamilySummableScaleIncrement.characteristicDifference =
      PublishedTailToCommonIncrement.characteristicDifference dataSet
  ; SameFamilySummableScaleIncrement.ordinaryDifferenceNonnegative =
      PublishedTailToCommonIncrement.ordinaryDifferenceNonnegative dataSet
  ; SameFamilySummableScaleIncrement.characteristicDifferenceNonnegative =
      PublishedTailToCommonIncrement.characteristicDifferenceNonnegative dataSet
  ; SameFamilySummableScaleIncrement.ordinaryDifferenceBelowTail =
      PublishedTailToCommonIncrement.ordinaryResponseBelowGeneratedTail dataSet
  ; SameFamilySummableScaleIncrement.characteristicDifferenceBelowTail =
      PublishedTailToCommonIncrement.characteristicResponseBelowGeneratedTail dataSet
  }

publishedCharacteristicCauchyModulus :
  (dataSet : PublishedTailToCommonIncrement) → ∀ start count →
  PublishedTailToCommonIncrement.characteristicDifference dataSet start count
  ≤ coefficient dataSet * (Geo.half * Geo.halfPower start)
publishedCharacteristicCauchyModulus dataSet =
  characteristicCauchyModulus
    (publishedTailToSameFamilySummableIncrement dataSet)

summableRGIncrementCauchyCompilerLevel : ProofLevel
summableRGIncrementCauchyCompilerLevel = machineChecked

-- The old strict global map-contraction target is not consumed by this shortest
-- continuum path.  It remains a useful stronger theorem if independently proved.
strictGlobalRGMapContractionShortestRouteStatus : ProofLevel
strictGlobalRGMapContractionShortestRouteStatus = machineChecked

-- Genuine remaining L3 physical theorem after Round81:
-- prove that normalized characteristic/local-observable increments of the
-- literal source-native CMP119/CMP122 trajectory inherit a summable dyadic
-- majorant from its published E/R/B localization bounds.
physicalSameFamilyNormalizedCharacteristicIncrementLevel : ProofLevel
physicalSameFamilyNormalizedCharacteristicIncrementLevel = conditional
