module DASHI.Physics.Closure.NSTriadKNHHBadLiteralPositiveGainRound43Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 42 proved the literal Fourier vorticity production is order zero in a
-- common HH frequency scale and that direct comparison with viscous enstrophy
-- transports with two inverse powers.  The outstanding same-object issue was
-- that Round 39's RawBadGainSample stored an arbitrary nonnegative scalar.
--
-- This file removes that ambiguity for the positive-production part.  A
-- LiteralPositiveBadGainCell owns the actual Fourier modes and defines the
-- Round-39 rawGain *definitionally* to be the actual ordered enstrophy
-- production.  The bad mask is the same BadTaggedEnergySample used by the
-- restricted viscous charge.  Therefore no independent raw-gain scalar can be
-- inserted between the physical production and the owner estimate.
--
-- The exact bridge proved below is the requested
--
--   physicalLiteralProductionToRawBadGainSameObject.
--
-- It converts a literal production-density estimate directly into the existing
-- RestrictedGainDensityCell.  A finite list conversion then gives the exact
-- Round-39 cell family.  Finally, when the density is the Round-42
-- inverse-square gain C 2^(-2q), the existing theorem that inverse-square beats
-- the mature Round-33 requirement constructs an InverseShellRestrictedGainDensity
-- certificate without reintroducing the old half-kernel loss.
--
-- Important boundary: this does not assert that the whole positive nonlinear
-- shell gain has already been decomposed into these literal positive-production
-- cells.  That decomposition is now the remaining physical identification,
-- rather than an unconstrained rawGain field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicBiotSavartMultiplierExact as Biot
import DASHI.Physics.Closure.NSTriadKNHHBadLiteralVorticityInteractionScalingRound42Exact as Literal
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedDissipationRound38Exact as Bad
import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedGainDensityRound39Exact as Gain
import DASHI.Physics.Closure.NSTriadKNHHBadSharpDyadicGainRound33Exact as Sharp
import DASHI.Physics.Closure.NSTriadKNHHBadDissipativeFloorChargingRound36Exact as Floor
import DASHI.Physics.Closure.NSTriadKNHHBadInverseSquareBeatsRequiredGainRound42Exact as InverseSquare

record LiteralPositiveBadGainCell
    (effectiveViscosity density : ℚ)
    (shell : Nat) : Set where
  constructor literal-positive-bad-gain-cell
  field
    energySample : Bad.BadTaggedEnergySample
    outputVorticity : Gram.Vec3
    leftMode rightMode : Biot.NonzeroVorticityMode

    badEvidence : Bad.isBad energySample ≡ true

    literalProductionNonnegative :
      0ℚ ≤ Literal.orderedEnstrophyProduction
        outputVorticity leftMode rightMode

    viscousChargeNonnegative :
      0ℚ ≤ Bad.maskedViscousCharge
        effectiveViscosity shell energySample

    literalProductionDensityBound :
      Literal.orderedEnstrophyProduction
        outputVorticity leftMode rightMode
      ≤ density * Bad.maskedViscousCharge
          effectiveViscosity shell energySample

open LiteralPositiveBadGainCell public

literalRawBadGainSample :
  ∀ {effectiveViscosity density shell} →
  LiteralPositiveBadGainCell effectiveViscosity density shell →
  Gain.RawBadGainSample
literalRawBadGainSample cell =
  Gain.raw-bad-gain-sample
    (energySample cell)
    (Literal.orderedEnstrophyProduction
      (outputVorticity cell) (leftMode cell) (rightMode cell))
    (literalProductionNonnegative cell)

rawGainIsLiteralProduction :
  ∀ {effectiveViscosity density shell}
    (cell : LiteralPositiveBadGainCell effectiveViscosity density shell) →
  Gain.rawGain (literalRawBadGainSample cell)
  ≡ Literal.orderedEnstrophyProduction
      (outputVorticity cell) (leftMode cell) (rightMode cell)
rawGainIsLiteralProduction cell = refl

maskedLiteralGainExact :
  ∀ {effectiveViscosity density shell}
    (cell : LiteralPositiveBadGainCell effectiveViscosity density shell) →
  Gain.maskedGain (literalRawBadGainSample cell)
  ≡ Literal.orderedEnstrophyProduction
      (outputVorticity cell) (leftMode cell) (rightMode cell)
maskedLiteralGainExact cell =
  Gain.maskedGainBadSampleExact
    (literalRawBadGainSample cell)
    (badEvidence cell)

physicalLiteralProductionToRawBadGainSameObject :
  ∀ {effectiveViscosity density shell} →
  LiteralPositiveBadGainCell effectiveViscosity density shell →
  Gain.RestrictedGainDensityCell effectiveViscosity density shell
physicalLiteralProductionToRawBadGainSameObject
    {effectiveViscosity} {density} {shell} cell =
  Gain.restricted-gain-density-cell
    (literalRawBadGainSample cell)
    (viscousChargeNonnegative cell)
    translatedBound
  where
  translatedBound :
    Gain.maskedGain (literalRawBadGainSample cell)
    ≤ density * Bad.maskedViscousCharge
        effectiveViscosity shell (energySample cell)
  translatedBound =
    subst
      (λ lower →
        lower
        ≤ density * Bad.maskedViscousCharge
            effectiveViscosity shell (energySample cell))
      (sym (maskedLiteralGainExact cell))
      (literalProductionDensityBound cell)

physicalHHBadGainDensityCellsFromLiteralProduction :
  ∀ {effectiveViscosity density shell} →
  List (LiteralPositiveBadGainCell effectiveViscosity density shell) →
  List (Gain.RestrictedGainDensityCell effectiveViscosity density shell)
physicalHHBadGainDensityCellsFromLiteralProduction [] = []
physicalHHBadGainDensityCellsFromLiteralProduction (cell ∷ rest) =
  physicalLiteralProductionToRawBadGainSameObject cell
  ∷ physicalHHBadGainDensityCellsFromLiteralProduction rest

inverseSquareGainNonnegative :
  ∀ coefficient shell →
  0ℚ ≤ coefficient →
  0ℚ ≤ InverseSquare.inverseSquareGain coefficient shell
inverseSquareGainNonnegative coefficient shell coefficientNN =
  let
    mu = Sharp.inverseDyadicScale shell
    muNN = Floor.inverseDyadicScaleNonnegative shell
    instance
      coefficientNNI = nonNegative coefficientNN
      muNNI = nonNegative muNN
      firstNNI = ℚP.nonNeg*nonNeg⇒nonNeg coefficient mu
      secondNNI = ℚP.nonNeg*nonNeg⇒nonNeg (coefficient * mu) mu
  in
  ℚP.nonNegative⁻¹ (InverseSquare.inverseSquareGain coefficient shell)

physicalInverseSquareGainDensityFromLiteralProduction :
  ∀ coefficient eta effectiveViscosity shell →
  0ℚ ≤ coefficient →
  coefficient ≤ eta * Sharp.half →
  List
    (LiteralPositiveBadGainCell
      effectiveViscosity
      (InverseSquare.inverseSquareGain coefficient shell)
      shell) →
  Gain.InverseShellRestrictedGainDensity effectiveViscosity shell
physicalInverseSquareGainDensityFromLiteralProduction
    coefficient eta effectiveViscosity shell coefficientNN coefficientBelow cells =
  record
    { density = InverseSquare.inverseSquareGain coefficient shell
    ; densityNonnegative = densityNN
    ; inverseShellTarget = Sharp.requiredHHBadGain eta shell
    ; inverseShellTargetNonnegative = ℚP.≤-trans densityNN densityBelow
    ; densityBelowInverseShellTarget = densityBelow
    ; cells = physicalHHBadGainDensityCellsFromLiteralProduction cells
    }
  where
  densityNN :
    0ℚ ≤ InverseSquare.inverseSquareGain coefficient shell
  densityNN = inverseSquareGainNonnegative coefficient shell coefficientNN

  densityBelow :
    InverseSquare.inverseSquareGain coefficient shell
    ≤ Sharp.requiredHHBadGain eta shell
  densityBelow =
    InverseSquare.inverseSquareGainBelowRequiredHHBadGain
      coefficient eta shell coefficientNN coefficientBelow

literalPositiveRawGainSameObjectClosed : Bool
literalPositiveRawGainSameObjectClosed = true

inverseSquareLiteralGainFeedsRound39DensityClosed : Bool
inverseSquareLiteralGainFeedsRound39DensityClosed = true

physicalPositiveShellGainDecompositionStillRequired : Bool
physicalPositiveShellGainDecompositionStillRequired = true

literalPositiveRawGainSameObjectClosedIsTrue :
  literalPositiveRawGainSameObjectClosed ≡ true
literalPositiveRawGainSameObjectClosedIsTrue = refl

inverseSquareLiteralGainFeedsRound39DensityClosedIsTrue :
  inverseSquareLiteralGainFeedsRound39DensityClosed ≡ true
inverseSquareLiteralGainFeedsRound39DensityClosedIsTrue = refl
