module DASHI.Moonshine.OggSSPP2Gamma0FourSubgroupIsogenyChainBidiExact where

------------------------------------------------------------------------
-- p=2 GAMMA_0(4) SUBGROUP DATA <-> TWO-ISOGENY-CHAIN PRESENTATION
--
-- DASHI CONTRIBUTION
--
-- The repository now has two source-facing presentations of the same intended
-- interior Gamma_0(4) arithmetic object:
--
--   finite-flat subgroup datum  (E, C2 <= C4)
--   length-two degree-2 isogeny chain.
--
-- This module states the exact BIDI grade required before those presentations
-- may be called the same arithmetic object.  It requires two-sided recovery
-- plus explicit compatibility of the first kernel with C2 and the composite
-- kernel with C4.
--
-- No arithmetic inhabitant is constructed here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSPP2Gamma0FourMarkedSubgroupSchemeSourceExact as Subgroup
import DASHI.Moonshine.OggSSPP2Gamma0FourTwoIsogenyChainSourceExact as Chain
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

record Gamma0FourSubgroupIsogenyChainBidi : Set₁ where
  field
    SubgroupState : Set
    ChainState : Set

    subgroupDatum :
      SubgroupState ->
      Subgroup.Gamma0FourFiniteFlatDatum

    chainDatum :
      ChainState ->
      Chain.Gamma0FourTwoIsogenyChain

    subgroupToChain :
      SubgroupState ->
      ChainState

    chainToSubgroup :
      ChainState ->
      SubgroupState

    subgroupRoundTrip :
      (state : SubgroupState) ->
      chainToSubgroup (subgroupToChain state) ≡ state

    chainRoundTrip :
      (state : ChainState) ->
      subgroupToChain (chainToSubgroup state) ≡ state

    firstKernelMatchesSelectedOrderTwoSubflag :
      (state : ChainState) ->
      Bool

    firstKernelMatchesSelectedOrderTwoSubflagIsTrue :
      (state : ChainState) ->
      firstKernelMatchesSelectedOrderTwoSubflag state ≡ true

    compositeKernelMatchesSelectedOrderFourSubgroup :
      (state : ChainState) ->
      Bool

    compositeKernelMatchesSelectedOrderFourSubgroupIsTrue :
      (state : ChainState) ->
      compositeKernelMatchesSelectedOrderFourSubgroup state ≡ true

    finiteFlatBadPrimeSemanticsPreserved :
      (state : ChainState) ->
      Bool

    finiteFlatBadPrimeSemanticsPreservedIsTrue :
      (state : ChainState) ->
      finiteFlatBadPrimeSemanticsPreserved state ≡ true

open Gamma0FourSubgroupIsogenyChainBidi public

subgroupToChainInjective :
  (bidi : Gamma0FourSubgroupIsogenyChainBidi) ->
  {left right : SubgroupState bidi} ->
  subgroupToChain bidi left ≡ subgroupToChain bidi right ->
  left ≡ right
subgroupToChainInjective bidi {left} {right} same
  rewrite sym (subgroupRoundTrip bidi left)
        | sym (subgroupRoundTrip bidi right)
        | same = refl

chainToSubgroupInjective :
  (bidi : Gamma0FourSubgroupIsogenyChainBidi) ->
  {left right : ChainState bidi} ->
  chainToSubgroup bidi left ≡ chainToSubgroup bidi right ->
  left ≡ right
chainToSubgroupInjective bidi {left} {right} same
  rewrite sym (chainRoundTrip bidi left)
        | sym (chainRoundTrip bidi right)
        | same = refl

data OneWayChainComparisonCreatesBidi : Set where
data DegreePatternCreatesBidi : Set where

oneWayChainComparisonDoesNotCreateBidi :
  OneWayChainComparisonCreatesBidi -> ⊥
oneWayChainComparisonDoesNotCreateBidi ()

degreePatternDoesNotCreateBidi :
  DegreePatternCreatesBidi -> ⊥
degreePatternDoesNotCreateBidi ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record Gamma0FourSubgroupIsogenyChainBidiBoundary : Set where
  constructor gamma0-four-subgroup-isogeny-chain-bidi-boundary
  field
    subgroupToChainMapRequired : Bool
    chainToSubgroupMapRequired : Bool
    twoSidedRecoveryRequired : Bool
    subflagCompatibilityRequired : Bool
    compositeKernelCompatibilityRequired : Bool
    finiteFlatSemanticsRequired : Bool
    arithmeticBidiConstructed : Bool

canonicalGamma0FourSubgroupIsogenyChainBidiBoundary :
  Gamma0FourSubgroupIsogenyChainBidiBoundary
canonicalGamma0FourSubgroupIsogenyChainBidiBoundary =
  gamma0-four-subgroup-isogeny-chain-bidi-boundary
    true true true true true true false
