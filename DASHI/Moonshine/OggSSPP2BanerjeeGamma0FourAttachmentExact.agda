module DASHI.Moonshine.OggSSPP2BanerjeeGamma0FourAttachmentExact where

------------------------------------------------------------------------
-- BANERJEE F4 UNIVERSAL DEFORMATION + PROOF-BEARING GAMMA_0(4) ATTACHMENT
--
-- Agda does not yet construct W(F4)[[a1]], so the selected elliptic object is
-- tied to the Banerjee source authority abstractly rather than definitionally.
--
-- A lawful attachment supplies:
--   * one finite-flat cyclic rank-4 subgroup;
--   * its rank-2 subflag;
--   * Gamma_0(4) bad-prime semantics;
--   * raw Frobenius on the reconstructed ten sectors;
--   * raw-Frobenius coarse-F4 invariance;
--   * commutation with the source-native Banerjee Galois involution.
--
-- The natural Galois action is NOT reused as raw Frobenius.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.OggSSPP2BanerjeeF4UniversalDeformationSourceExact as Banerjee
import DASHI.Moonshine.OggSSPP2BanerjeeF4SameSourceRealizationExact as SameSource
import DASHI.Moonshine.OggSSPP2BanerjeeGaloisVsF4OrbitNoGoExact as GaloisNoGo
import DASHI.Moonshine.OggSSPP2Gamma0FourMarkedSubgroupSchemeSourceExact as Gamma
import DASHI.Moonshine.OggSSPP2TwoInvolutionArithmeticSourceExact as Two
import DASHI.Moonshine.OggSSPP2F4FrobeniusCandidateNoGoExact as F4
import DASHI.Moonshine.OggSSPP2F4AntipodalStratifiedRefinementExact as Target
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

record BanerjeeGamma0FourAttachment
  (authority : SameSource.BanerjeeF4SourceAuthority) : Set₁ where
  field
    OrderFourSubgroup : Set
    OrderTwoSubgroup : Set

    selectedEllipticObject :
      SameSource.Universal.EllipticFamilyState
        (SameSource.datum authority)

    selectedOrderFourSubgroup :
      OrderFourSubgroup

    selectedOrderTwoSubgroup :
      OrderTwoSubgroup

    orderTwoSubflagOfOrderFour :
      Bool

    orderTwoSubflagOfOrderFourIsTrue :
      orderTwoSubflagOfOrderFour ≡ true

    finiteFlatAtCharacteristicTwo :
      Bool

    finiteFlatAtCharacteristicTwoIsTrue :
      finiteFlatAtCharacteristicTwo ≡ true

    gammaZeroLevelFourSemantics :
      Bool

    gammaZeroLevelFourSemanticsIsTrue :
      gammaZeroLevelFourSemantics ≡ true

    rawFrobenius :
      Banerjee.GaloisInertiaState ->
      Banerjee.GaloisInertiaState

    rawFrobeniusInvolutive :
      (state : Banerjee.GaloisInertiaState) ->
      rawFrobenius (rawFrobenius state) ≡ state

    rawFrobeniusPreservesCoarseOrbit :
      (state : Banerjee.GaloisInertiaState) ->
      Target.stratumOf (Banerjee.toTarget (rawFrobenius state))
      ≡
      Target.stratumOf (Banerjee.toTarget state)

    rawFrobeniusCommutesWithGalois :
      (state : Banerjee.GaloisInertiaState) ->
      rawFrobenius (GaloisNoGo.galoisInvolution state)
      ≡
      GaloisNoGo.galoisInvolution (rawFrobenius state)

    sourceReference :
      String

open BanerjeeGamma0FourAttachment public

finiteFlatDatum :
  {authority : SameSource.BanerjeeF4SourceAuthority} ->
  BanerjeeGamma0FourAttachment authority ->
  Gamma.Gamma0FourFiniteFlatDatum
finiteFlatDatum {authority} attachment =
  record
    { EllipticObject =
        SameSource.Universal.EllipticFamilyState
          (SameSource.datum authority)
    ; OrderFourSubgroup =
        OrderFourSubgroup attachment
    ; OrderTwoSubgroup =
        OrderTwoSubgroup attachment
    ; selectedEllipticObject =
        selectedEllipticObject attachment
    ; selectedOrderFourSubgroup =
        selectedOrderFourSubgroup attachment
    ; selectedOrderTwoSubgroup =
        selectedOrderTwoSubgroup attachment
    ; orderFourRank =
        4
    ; orderFourRankIsFour =
        refl
    ; orderTwoRank =
        2
    ; orderTwoRankIsTwo =
        refl
    ; orderTwoSubflagOfOrderFour =
        orderTwoSubflagOfOrderFour attachment
    ; orderTwoSubflagOfOrderFourIsTrue =
        orderTwoSubflagOfOrderFourIsTrue attachment
    ; finiteFlatAtCharacteristicTwo =
        finiteFlatAtCharacteristicTwo attachment
    ; finiteFlatAtCharacteristicTwoIsTrue =
        finiteFlatAtCharacteristicTwoIsTrue attachment
    ; gammaZeroLevelFourSemantics =
        gammaZeroLevelFourSemantics attachment
    ; gammaZeroLevelFourSemanticsIsTrue =
        gammaZeroLevelFourSemanticsIsTrue attachment
    ; sourceReference =
        sourceReference attachment
    }

coarseOrbit :
  Banerjee.GaloisInertiaState ->
  F4.F4FrobeniusOrbit
coarseOrbit state =
  Target.stratumOf (Banerjee.toTarget state)

twoInvolutionSource :
  {authority : SameSource.BanerjeeF4SourceAuthority} ->
  (attachment : BanerjeeGamma0FourAttachment authority) ->
  Two.TwoInvolutionSource
twoInvolutionSource attachment =
  record
    { datum =
        finiteFlatDatum attachment
    ; MarkedState =
        Banerjee.GaloisInertiaState
    ; rawFrobenius =
        rawFrobenius attachment
    ; rawFrobeniusInvolutive =
        rawFrobeniusInvolutive attachment
    ; galoisTransport =
        GaloisNoGo.galoisInvolution
    ; galoisTransportInvolutive =
        GaloisNoGo.galoisInvolutionInvolutive
    ; coarseF4Orbit =
        coarseOrbit
    ; rawFrobeniusPreservesCoarseOrbit =
        rawFrobeniusPreservesCoarseOrbit attachment
    ; actionsCommute =
        rawFrobeniusCommutesWithGalois attachment
    ; galoisTransportMayMoveCoarseOrbitAtCentre =
        true
    ; galoisTransportMayMoveCoarseOrbitAtCentreIsTrue =
        refl
    }

rawFrobeniusSource :
  {authority : SameSource.BanerjeeF4SourceAuthority} ->
  BanerjeeGamma0FourAttachment authority ->
  Gamma.Gamma0FourMarkedArithmeticSource
rawFrobeniusSource attachment =
  Two.toRawFrobeniusSource (twoInvolutionSource attachment)

naturalGaloisCannotBeRawFrobenius :
  GaloisNoGo.GloballyInvariantCoarseOrbit ->
  ⊥
naturalGaloisCannotBeRawFrobenius =
  GaloisNoGo.naturalGaloisCannotPreserveCurrentCoarseOrbit

data BanerjeeGamma0FourAttachmentResidual : Set where
  missingFiniteFlatOrderFourSubgroup :
    BanerjeeGamma0FourAttachmentResidual

  missingOrderTwoSubflag :
    BanerjeeGamma0FourAttachmentResidual

  missingRawFrobeniusOnAttachedLevelStructure :
    BanerjeeGamma0FourAttachmentResidual

  missingRawGaloisCommutation :
    BanerjeeGamma0FourAttachmentResidual

firstResidual :
  BanerjeeGamma0FourAttachmentResidual
firstResidual =
  missingFiniteFlatOrderFourSubgroup

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record BanerjeeGamma0FourAttachmentBoundary : Set where
  constructor banerjee-gamma0-four-attachment-boundary
  field
    ellipticObjectBoundToBanerjeeAuthority : Bool
    finiteFlatDatumProofBearing : Bool
    naturalGaloisTransportFixed : Bool
    naturalGaloisRejectedAsRawFrobenius : Bool
    rawFrobeniusRequiredSeparately : Bool
    rawGaloisCommutationRequired : Bool
    twoInvolutionSourceConstructedAutomatically : Bool
    attachmentInhabitedHere : Bool

canonicalBanerjeeGamma0FourAttachmentBoundary :
  BanerjeeGamma0FourAttachmentBoundary
canonicalBanerjeeGamma0FourAttachmentBoundary =
  banerjee-gamma0-four-attachment-boundary
    true true true true true true true false
