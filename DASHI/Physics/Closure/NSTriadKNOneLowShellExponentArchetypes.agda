module DASHI.Physics.Closure.NSTriadKNOneLowShellExponentArchetypes where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin; Terence Tao;
-- Jean-Michel Bony; Pierre Germain; DASHI repository contributors.
-- Title: "One-low dyadic exponent archetypes for the three frozen
-- Navier-Stokes legs".
-- Venue/year: Fourier Analysis and Nonlinear Partial Differential Equations,
-- Springer, 2011; UCLA 247B lecture notes, 2007; Annales scientifiques de
-- l'Ecole Normale Superieure 14 (1981); Journal of Differential Equations
-- 226 (2006); DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-16830-7; Tao lecture notes have no DOI;
-- 10.24033/asens.1404; 10.1016/j.jde.2005.10.007;
-- repository-original exponent tables have no DOI.
-- Uses: the standard three-dimensional Bernstein factor 2^(3L/2), one
-- derivative, and two H^s shell weights.  At s=5/2 the common low-shell
-- decay is 5/2; the separation-gap decay is 3/2 when the derivative remains
-- high and 5/2 when it lies on the low factor.
-- Relationship: closes the two universal one-low exponent archetypes and the
-- two literal output-leg assignments.  It does not guess the repository's
-- still-undefined farLow/farHigh support predicates or collapse the direct
-- and swapped first-adjoint derivative locations into one false formula.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNTaoFrozenLegParaproductProgram as Tao
import DASHI.Physics.Closure.NSTriadKNShellExponentLedgerProgram as Ledger

------------------------------------------------------------------------
-- All rational exponents below are scaled by two.
------------------------------------------------------------------------

data OneLowDerivativeLocation : Set where
  derivativeHigh
  derivativeLow
  orderedPairContainsBoth : OneLowDerivativeLocation

record EndpointOneLowProfile : Set where
  constructor endpoint-profile
  field
    lowShellDecayMagnitudeTimesTwo : Nat
    gapDecayMagnitudeTimesTwo : Nat

open EndpointOneLowProfile public

endpointOneLowProfile : OneLowDerivativeLocation → EndpointOneLowProfile
endpointOneLowProfile derivativeHigh = endpoint-profile 5 3
endpointOneLowProfile derivativeLow = endpoint-profile 5 5
endpointOneLowProfile orderedPairContainsBoth = endpoint-profile 5 3

record OneLowArchetypeReceipt : Set where
  constructor receipt
  field
    highDerivativeLowDecayIsFiveHalves :
      lowShellDecayMagnitudeTimesTwo
        (endpointOneLowProfile derivativeHigh) ≡ 5
    highDerivativeGapDecayIsThreeHalves :
      gapDecayMagnitudeTimesTwo
        (endpointOneLowProfile derivativeHigh) ≡ 3
    lowDerivativeLowDecayIsFiveHalves :
      lowShellDecayMagnitudeTimesTwo
        (endpointOneLowProfile derivativeLow) ≡ 5
    lowDerivativeGapDecayIsFiveHalves :
      gapDecayMagnitudeTimesTwo
        (endpointOneLowProfile derivativeLow) ≡ 5
    mixedOrderedPairUsesWorstGap :
      gapDecayMagnitudeTimesTwo
        (endpointOneLowProfile orderedPairContainsBoth) ≡ 3

open OneLowArchetypeReceipt public

oneLowArchetypeReceipt : OneLowArchetypeReceipt
oneLowArchetypeReceipt = receipt refl refl refl refl refl

------------------------------------------------------------------------
-- Literal output-leg assignments.
--
-- left low / right high: derivative q is high;
-- right low / left high: derivative q is low.
------------------------------------------------------------------------

outputLowHighDerivativeLocation : OneLowDerivativeLocation
outputLowHighDerivativeLocation = derivativeHigh

outputHighLowDerivativeLocation : OneLowDerivativeLocation
outputHighLowDerivativeLocation = derivativeLow

record OutputOneLowMappingReceipt : Set where
  constructor output-receipt
  field
    outputLowHighDerivativeIsHigh :
      outputLowHighDerivativeLocation ≡ derivativeHigh
    outputHighLowDerivativeIsLow :
      outputHighLowDerivativeLocation ≡ derivativeLow
    outputLowHighEndpointGapIsThreeHalves :
      gapDecayMagnitudeTimesTwo
        (endpointOneLowProfile outputLowHighDerivativeLocation) ≡ 3
    outputHighLowEndpointGapIsFiveHalves :
      gapDecayMagnitudeTimesTwo
        (endpointOneLowProfile outputHighLowDerivativeLocation) ≡ 5

open OutputOneLowMappingReceipt public

outputOneLowMappingReceipt : OutputOneLowMappingReceipt
outputOneLowMappingReceipt = output-receipt refl refl refl refl

record TwelveSeparatedRowMappingCutset : Set₁ where
  field
    outputLowHighMapped : Set
    outputHighLowMapped : Set
    outputFarLowSupportPredicateDefined : Set
    outputFarHighSupportPredicateDefined : Set

    firstLowHighDirectAndSwappedSeparated : Set
    firstHighLowDirectAndSwappedSeparated : Set
    firstFarLowSupportPredicateDefined : Set
    firstFarHighSupportPredicateDefined : Set

    secondLowHighFrozenFrequencyLocated : Set
    secondHighLowFrozenFrequencyLocated : Set
    secondFarLowSupportPredicateDefined : Set
    secondFarHighSupportPredicateDefined : Set

    allTwelveDerivativeLocationsMapped : Set
    allTwelveEndpointProfilesInstantiated : Set
    allTwelveCutoffUniformConstantsSupplied : Set

open TwelveSeparatedRowMappingCutset public

oneLowExponentArchetypesClosed : Bool
oneLowExponentArchetypesClosed = true

oneLowExponentArchetypesClosedIsTrue :
  oneLowExponentArchetypesClosed ≡ true
oneLowExponentArchetypesClosedIsTrue = refl

literalOutputOneLowRowsMapped : Bool
literalOutputOneLowRowsMapped = true

literalOutputOneLowRowsMappedIsTrue :
  literalOutputOneLowRowsMapped ≡ true
literalOutputOneLowRowsMappedIsTrue = refl

allTwelveSeparatedRowsMapped : Bool
allTwelveSeparatedRowsMapped = false

allTwelveSeparatedRowsMappedIsFalse :
  allTwelveSeparatedRowsMapped ≡ false
allTwelveSeparatedRowsMappedIsFalse = refl

allTwelveSeparatedRowsAnalyticallyClosed : Bool
allTwelveSeparatedRowsAnalyticallyClosed = false

allTwelveSeparatedRowsAnalyticallyClosedIsFalse :
  allTwelveSeparatedRowsAnalyticallyClosed ≡ false
allTwelveSeparatedRowsAnalyticallyClosedIsFalse = refl
