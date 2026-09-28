module DASHI.Moonshine.OggSSPP2UniqueGamma0FourMarkingBidiExact where

------------------------------------------------------------------------
-- p=2 UNIQUE ker(F^2) MARKING <-> PAID TEN-STATE TARGET, BIDI CONTRACT
--
-- DASHI CONTRIBUTION
--
-- The raw supersingular Gamma_0(4) subgroup choice is already separated:
-- there is one raw subgroup, ker(F^2), while the residual target has ten
-- states.  Therefore any successful arithmetic source must add marked
-- residual data OVER that unique subgroup.
--
-- This module packages the strongest lawful same-object target:
--
--   future arithmetic marked state
--      <-> F4StratifiedTargetState
--
-- with exact two-sided state recovery and exact preservation of the three
-- F4/F2 coarse Frobenius strata.
--
-- The record is intentionally uninhabited here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Moonshine.OggSSPP2Gamma0FourUniqueSupersingularSubgroupSeparationExact as Unique
import DASHI.Moonshine.OggSSPP2F4FrobeniusCandidateNoGoExact as F4
import DASHI.Moonshine.OggSSPP2F4AntipodalStratifiedRefinementExact as Target
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

record UniqueGamma0FourMarkingBidi
  (source : Unique.MarkingOverUniqueGamma0FourSubgroup) : Set₁ where
  field
    sourceCoarseOrbit :
      Unique.MarkedState source ->
      F4.F4FrobeniusOrbit

    toTarget :
      Unique.MarkedState source ->
      Target.F4StratifiedTargetState

    fromTarget :
      Target.F4StratifiedTargetState ->
      Unique.MarkedState source

    sourceRoundTrip :
      (state : Unique.MarkedState source) ->
      fromTarget (toTarget state) ≡ state

    targetRoundTrip :
      (state : Target.F4StratifiedTargetState) ->
      toTarget (fromTarget state) ≡ state

    toTargetPreservesCoarseOrbit :
      (state : Unique.MarkedState source) ->
      Target.stratumOf (toTarget state)
      ≡ sourceCoarseOrbit state

    fromTargetPreservesCoarseOrbit :
      (state : Target.F4StratifiedTargetState) ->
      sourceCoarseOrbit (fromTarget state)
      ≡ Target.stratumOf state

    everyMappedStateStillLiesOverUniqueRawSubgroup :
      (state : Target.F4StratifiedTargetState) ->
      Unique.rawSubgroup source (fromTarget state)
      ≡ Unique.kerFrobeniusSquared

open UniqueGamma0FourMarkingBidi public

------------------------------------------------------------------------
-- Bidi implies both state maps are injective.
------------------------------------------------------------------------

toTargetInjective :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  (bidi : UniqueGamma0FourMarkingBidi source) ->
  {left right : Unique.MarkedState source} ->
  toTarget bidi left ≡ toTarget bidi right ->
  left ≡ right
toTargetInjective bidi {left} {right} same
  rewrite sym (sourceRoundTrip bidi left)
        | sym (sourceRoundTrip bidi right)
        | same = refl

fromTargetInjective :
  {source : Unique.MarkingOverUniqueGamma0FourSubgroup} ->
  (bidi : UniqueGamma0FourMarkingBidi source) ->
  {left right : Target.F4StratifiedTargetState} ->
  fromTarget bidi left ≡ fromTarget bidi right ->
  left ≡ right
fromTargetInjective bidi {left} {right} same
  rewrite sym (targetRoundTrip bidi left)
        | sym (targetRoundTrip bidi right)
        | same = refl

------------------------------------------------------------------------
-- Promotion firewall.
------------------------------------------------------------------------

data FibreCountsCreateMarkingBidi : Set where
data UniqueRawSubgroupCreatesMarkingBidi : Set where

fibreCountsDoNotCreateMarkingBidi :
  FibreCountsCreateMarkingBidi -> ⊥
fibreCountsDoNotCreateMarkingBidi ()

uniqueRawSubgroupDoesNotCreateMarkingBidi :
  UniqueRawSubgroupCreatesMarkingBidi -> ⊥
uniqueRawSubgroupDoesNotCreateMarkingBidi ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record UniqueGamma0FourMarkingBidiBoundary : Set where
  constructor unique-gamma0-four-marking-bidi-boundary
  field
    twoSidedStateRecoveryRequired : Bool
    coarseF4StratumPreservationRequiredBothWays : Bool
    uniqueRawSubgroupProvenanceRequired : Bool
    sourceTargetCardinalityAloneSufficient : Bool
    arithmeticBidiConstructed : Bool

canonicalUniqueGamma0FourMarkingBidiBoundary :
  UniqueGamma0FourMarkingBidiBoundary
canonicalUniqueGamma0FourMarkingBidiBoundary =
  unique-gamma0-four-marking-bidi-boundary
    true true true false false
