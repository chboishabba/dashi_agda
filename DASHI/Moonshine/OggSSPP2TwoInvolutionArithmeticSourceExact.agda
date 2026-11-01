module DASHI.Moonshine.OggSSPP2TwoInvolutionArithmeticSourceExact where

------------------------------------------------------------------------
-- p=2 TWO-INVOLUTION ARITHMETIC SOURCE
--
-- Separate:
--
--   * raw Frobenius on the F4/F2 arithmetic coordinate;
--   * Gal(F4/F2) transport on Banerjee's universal-deformation torsor.
--
-- The old Gamma0FourMarkedArithmeticSource remains the raw-Frobenius view,
-- where the coarse F4 orbit label is invariant.
--
-- Banerjee Galois transport is a second action.  It need not preserve the
-- current coarse orbit globally; the paid no-go localizes the failure to the
-- duplicated centre.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPP2Gamma0FourMarkedSubgroupSchemeSourceExact as Gamma
import DASHI.Moonshine.OggSSPP2F4FrobeniusCandidateNoGoExact as F4
import DASHI.Moonshine.OggSSPP2BanerjeeGaloisVsF4OrbitNoGoExact as GaloisNoGo
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

record TwoInvolutionSource : Set₁ where
  field
    datum :
      Gamma.Gamma0FourFiniteFlatDatum

    MarkedState : Set

    rawFrobenius :
      MarkedState -> MarkedState

    rawFrobeniusInvolutive :
      (state : MarkedState) ->
      rawFrobenius (rawFrobenius state) ≡ state

    galoisTransport :
      MarkedState -> MarkedState

    galoisTransportInvolutive :
      (state : MarkedState) ->
      galoisTransport (galoisTransport state) ≡ state

    coarseF4Orbit :
      MarkedState ->
      F4.F4FrobeniusOrbit

    rawFrobeniusPreservesCoarseOrbit :
      (state : MarkedState) ->
      coarseF4Orbit (rawFrobenius state)
      ≡ coarseF4Orbit state

    actionsCommute :
      (state : MarkedState) ->
      rawFrobenius (galoisTransport state)
      ≡ galoisTransport (rawFrobenius state)

    galoisTransportMayMoveCoarseOrbitAtCentre :
      Bool

    galoisTransportMayMoveCoarseOrbitAtCentreIsTrue :
      galoisTransportMayMoveCoarseOrbitAtCentre ≡ true

open TwoInvolutionSource public

toRawFrobeniusSource :
  TwoInvolutionSource ->
  Gamma.Gamma0FourMarkedArithmeticSource
toRawFrobeniusSource source =
  record
    { datum =
        datum source
    ; MarkedState =
        MarkedState source
    ; frobenius =
        rawFrobenius source
    ; frobeniusInvolutive =
        rawFrobeniusInvolutive source
    ; coarseF4Orbit =
        coarseF4Orbit source
    ; coarseF4OrbitInvariant =
        rawFrobeniusPreservesCoarseOrbit source
    }

banerjeeGaloisNotGloballyCoarseInvariant :
  GaloisNoGo.GloballyInvariantCoarseOrbit ->
  ⊥
banerjeeGaloisNotGloballyCoarseInvariant =
  GaloisNoGo.naturalGaloisCannotPreserveCurrentCoarseOrbit

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record TwoInvolutionArithmeticSourceBoundary : Set where
  constructor two-involution-arithmetic-source-boundary
  field
    rawFrobeniusSeparated : Bool
    banerjeeGaloisTransportSeparated : Bool
    rawFrobeniusCoarseInvarianceRetained : Bool
    galoisGlobalCoarseInvarianceRequired : Bool
    actionCommutationRequired : Bool
    oldRawFrobeniusSourceRecoverable : Bool

canonicalTwoInvolutionArithmeticSourceBoundary :
  TwoInvolutionArithmeticSourceBoundary
canonicalTwoInvolutionArithmeticSourceBoundary =
  two-involution-arithmetic-source-boundary
    true true true false true true
