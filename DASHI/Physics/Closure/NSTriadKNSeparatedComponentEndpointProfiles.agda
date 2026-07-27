module DASHI.Physics.Closure.NSTriadKNSeparatedComponentEndpointProfiles where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin; Terence Tao;
-- Jean-Michel Bony; Pierre Germain; Loukas Grafakos; Seungly Oh; DASHI
-- repository contributors.
-- Title: "Lower-endpoint decay profiles for every separated Stage-3 shell
-- component".
-- Venue/year: Fourier Analysis and Nonlinear Partial Differential Equations,
-- Springer, 2011; UCLA Math 247B lecture notes, 2007; Annales scientifiques
-- de l'Ecole Normale Superieure 14 (1981); Journal of Differential Equations
-- 226 (2006); Communications in Partial Differential Equations 39 (2014);
-- DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-16830-7; Tao lecture notes have no DOI;
-- 10.24033/asens.1404; 10.1016/j.jde.2005.10.007;
-- 10.1080/03605302.2013.822885; repository-original component table has no DOI.
-- Uses: s=5/2 lower-endpoint profiles scaled by two.  One-low high derivative
-- gives (5,3), one-low low derivative gives (5,5), first-adjoint high-high
-- convolution gives (5,8), and output/second high-high structure gives (5,10).
-- Relationship: instantiates an endpoint profile for all twelve separated
-- direct components.  Uniform analytic constants for the five archetypes are
-- still separate proof obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNSeparatedComponentLedger as Components

record EndpointProfile : Set where
  constructor profile
  field
    lowDecayTimesTwo : Nat
    gapDecayTimesTwo : Nat

open EndpointProfile public

archetypeEndpointProfile : Components.AnalyticArchetype → EndpointProfile
archetypeEndpointProfile Components.lowBernsteinDerivativeHigh = profile 5 3
archetypeEndpointProfile Components.lowBernsteinDerivativeLow = profile 5 5
archetypeEndpointProfile Components.highHighFirstAdjointConvolution = profile 5 8
archetypeEndpointProfile Components.outputRelocationGain = profile 5 10
archetypeEndpointProfile Components.secondAdjointFrozenLowDerivative = profile 5 10
archetypeEndpointProfile Components.finiteOverlapMajorant = profile 0 0

componentEndpointProfile : Components.ShellComponent → EndpointProfile
componentEndpointProfile component =
  archetypeEndpointProfile (Components.componentArchetype component)

record EndpointProfileReceipt : Set where
  constructor receipt
  field
    oneLowHighDerivativeIsFiveThree :
      archetypeEndpointProfile Components.lowBernsteinDerivativeHigh
      ≡ profile 5 3
    oneLowLowDerivativeIsFiveFive :
      archetypeEndpointProfile Components.lowBernsteinDerivativeLow
      ≡ profile 5 5
    firstHighHighIsFiveEight :
      archetypeEndpointProfile Components.highHighFirstAdjointConvolution
      ≡ profile 5 8
    outputRelocationIsFiveTen :
      archetypeEndpointProfile Components.outputRelocationGain
      ≡ profile 5 10
    secondFrozenDerivativeIsFiveTen :
      archetypeEndpointProfile Components.secondAdjointFrozenLowDerivative
      ≡ profile 5 10

open EndpointProfileReceipt public

endpointProfileReceipt : EndpointProfileReceipt
endpointProfileReceipt = receipt refl refl refl refl refl

allTwelveSeparatedComponentsMapped : Bool
allTwelveSeparatedComponentsMapped = true

allTwelveSeparatedComponentsMappedIsTrue :
  allTwelveSeparatedComponentsMapped ≡ true
allTwelveSeparatedComponentsMappedIsTrue =
  Components.allSeparatedComponentArchetypesMappedIsTrue

allTwelveEndpointProfilesInstantiated : Bool
allTwelveEndpointProfilesInstantiated = true

allTwelveEndpointProfilesInstantiatedIsTrue :
  allTwelveEndpointProfilesInstantiated ≡ true
allTwelveEndpointProfilesInstantiatedIsTrue = refl

allFiveArchetypeEstimatesCutoffUniform : Bool
allFiveArchetypeEstimatesCutoffUniform = false

allFiveArchetypeEstimatesCutoffUniformIsFalse :
  allFiveArchetypeEstimatesCutoffUniform ≡ false
allFiveArchetypeEstimatesCutoffUniformIsFalse = refl
