module DASHI.Moonshine.OggSSPPBLocalizedDVRPreferredPaymentCutsetExact where

------------------------------------------------------------------------
-- pB LOCALIZED DVR -> PREFERRED GEOMETRIC PAYMENT CUTSET
--
-- PURPOSE
--
-- Remove the Monster target entirely from the missing analytic theorem.
--
-- Already-owned geometric payment presentations:
--
--   p=2:
--     five loop-reversal inertia sectors
--     with independent centralizer-depth weights
--
--       3, 3, 2, 1, 1
--
--   p=3:
--     Deligne--Rapoport local-incidence orbit sectors
--
--       node, branch-pair
--
--     with weights
--
--       1, 1.
--
-- Already-sourced mixed-characteristic structure:
--
--   * Carnahan: integral/mod-p pB Tate-cohomology centralizer object;
--   * Urano: finite-length DVR generalized Brauer character, normalized by
--     v(p), additive on short exact sequences and stable under finite DVR
--     extension.
--
-- THE ONLY MISSING ANALYTIC PAYMENT
--
-- Localize the SAME integral pB Tate object to the bad-level Igusa/wild
-- geometry, decompose it sectorwise over the already-defined local sectors,
-- and prove that its normalized finite-length multiplicities are exactly the
-- pre-existing geometric sector weights.
--
-- This authority is target-independent:
--   it contains no Monster order,
--   no Duncan--Swisher baseline,
--   and no literals 10 or 2 as requested outputs.
--
-- The totals 10/2 follow only AFTERWARDS from summing the independent sector
-- weights.  Existing modules may then compare those totals with Monster-local
-- defects as a separate recognition theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSPSmallPrimePBIntegralTateCohomologyBridgeExact as Tate
import DASHI.Moonshine.OggSSPSmallPrimeDVRLengthBrauerCutsetExact as DVR
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Target-independent sectorwise localization authority.
------------------------------------------------------------------------

record PBLocalizedDVRPreferredPaymentAuthority : Set₁ where
  field
    LocalizedPiece : Set

    p2Piece :
      Preferred.Sector Preferred.p2PreferredPresentation ->
      LocalizedPiece

    p3Piece :
      Preferred.Sector Preferred.p3PreferredPresentation ->
      LocalizedPiece

    normalizedDVRLength :
      LocalizedPiece ->
      Nat

    p2LengthMatchesIndependentGeometricWeight :
      (sector : Preferred.Sector Preferred.p2PreferredPresentation) ->
      normalizedDVRLength (p2Piece sector)
      ≡
      Preferred.weight Preferred.p2PreferredPresentation sector

    p3LengthMatchesIndependentGeometricWeight :
      (sector : Preferred.Sector Preferred.p3PreferredPresentation) ->
      normalizedDVRLength (p3Piece sector)
      ≡
      Preferred.weight Preferred.p3PreferredPresentation sector

    piecesComeFromCarnahanIntegralPBTateObject :
      Bool
    piecesComeFromCarnahanIntegralPBTateObjectIsTrue :
      piecesComeFromCarnahanIntegralPBTateObject ≡ true

    piecesComeFromPrimeEqualsLevelIgusaWildLocalization :
      Bool
    piecesComeFromPrimeEqualsLevelIgusaWildLocalizationIsTrue :
      piecesComeFromPrimeEqualsLevelIgusaWildLocalization ≡ true

    decompositionPreservesPBMonsterLocalCentralizerAction :
      Bool
    decompositionPreservesPBMonsterLocalCentralizerActionIsTrue :
      decompositionPreservesPBMonsterLocalCentralizerAction ≡ true

    generalizedBrauerCharacterCompatibleWithSectorDecomposition :
      Bool
    generalizedBrauerCharacterCompatibleWithSectorDecompositionIsTrue :
      generalizedBrauerCharacterCompatibleWithSectorDecomposition ≡ true

    lengthIsUranoNormalizedCompositionLength :
      Bool
    lengthIsUranoNormalizedCompositionLengthIsTrue :
      lengthIsUranoNormalizedCompositionLength ≡ true

    constructionUsesNoMonsterOrderTarget :
      Bool
    constructionUsesNoMonsterOrderTargetIsTrue :
      constructionUsesNoMonsterOrderTarget ≡ true

    constructionUsesNoDuncanSwisherResidualTarget :
      Bool
    constructionUsesNoDuncanSwisherResidualTargetIsTrue :
      constructionUsesNoDuncanSwisherResidualTarget ≡ true

open PBLocalizedDVRPreferredPaymentAuthority public

data PBLocalizedDVRPreferredPaymentAuthorityInhabited : Set where

pbLocalizedDVRPreferredPaymentStillOpen :
  PBLocalizedDVRPreferredPaymentAuthorityInhabited -> ⊥
pbLocalizedDVRPreferredPaymentStillOpen ()

------------------------------------------------------------------------
-- 2. Geometry determines the total only after the sectorwise theorem.
------------------------------------------------------------------------

p2IndependentGeometricTotal : Nat
p2IndependentGeometricTotal =
  Preferred.total Preferred.p2PreferredPresentation

p3IndependentGeometricTotal : Nat
p3IndependentGeometricTotal =
  Preferred.total Preferred.p3PreferredPresentation

p2IndependentGeometricTotalIsTen :
  p2IndependentGeometricTotal ≡ 10
p2IndependentGeometricTotalIsTen =
  Preferred.p2PreferredTotalIsTen

p3IndependentGeometricTotalIsTwo :
  p3IndependentGeometricTotal ≡ 2
p3IndependentGeometricTotalIsTwo =
  Preferred.p3PreferredTotalIsTwo

------------------------------------------------------------------------
-- 3. Existing source receipts.
------------------------------------------------------------------------

integralTateBoundary :
  Tate.PBIntegralTateBridgeBoundary
integralTateBoundary =
  Tate.canonicalPBIntegralTateBridgeBoundary

dvrBrauerBoundary :
  DVR.DVRLengthBrauerCutsetBoundary
dvrBrauerBoundary =
  DVR.canonicalDVRLengthBrauerCutsetBoundary

preferredPaymentBoundary :
  Preferred.PreferredCorrectionPaymentBoundary
preferredPaymentBoundary =
  Preferred.canonicalPreferredCorrectionPaymentBoundary

------------------------------------------------------------------------
-- 4. Fail-closed promotion rules.
------------------------------------------------------------------------

data SectorWeightsMayBeReadFromMonsterResidual : Set where
data TotalTenTwoMayDefineSectorLengths : Set where
data EqualityOfTotalsProvesSectorwiseLocalization : Set where
data UranoFrameworkAloneDeterminesGeometricWeights : Set where
data CarnahanTateObjectAloneDeterminesIgusaDecomposition : Set where

sectorWeightsMayNotBeReadFromMonsterResidual :
  SectorWeightsMayBeReadFromMonsterResidual -> ⊥
sectorWeightsMayNotBeReadFromMonsterResidual ()

totalTenTwoMayNotDefineSectorLengths :
  TotalTenTwoMayDefineSectorLengths -> ⊥
totalTenTwoMayNotDefineSectorLengths ()

equalTotalsDoNotProveSectorwiseLocalization :
  EqualityOfTotalsProvesSectorwiseLocalization -> ⊥
equalTotalsDoNotProveSectorwiseLocalization ()

uranoFrameworkDoesNotDetermineGeometricWeights :
  UranoFrameworkAloneDeterminesGeometricWeights -> ⊥
uranoFrameworkDoesNotDetermineGeometricWeights ()

carnahanTateObjectDoesNotDetermineIgusaDecomposition :
  CarnahanTateObjectAloneDeterminesIgusaDecomposition -> ⊥
carnahanTateObjectDoesNotDetermineIgusaDecomposition ()

------------------------------------------------------------------------
-- 5. Attribution boundary.
------------------------------------------------------------------------

data CarnahanCreditedWithSectorWeights : Set where
data UranoCreditedWithSectorWeights : Set where
data GeometricAuthorsCreditedWithMoonshineValuation : Set where

carnahanNotCreditedWithDASHISectorWeights :
  CarnahanCreditedWithSectorWeights -> ⊥
carnahanNotCreditedWithDASHISectorWeights ()

uranoNotCreditedWithDASHISectorWeights :
  UranoCreditedWithSectorWeights -> ⊥
uranoNotCreditedWithDASHISectorWeights ()

geometricSourcesNotCreditedWithMoonshineValuation :
  GeometricAuthorsCreditedWithMoonshineValuation -> ⊥
geometricSourcesNotCreditedWithMoonshineValuation ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record PBLocalizedDVRPreferredPaymentCutsetBoundary : Set where
  constructor pb-localized-dvr-preferred-payment-cutset-boundary
  field
    p2SectorWeightsIndependentlyOwned : Bool
    p3SectorWeightsIndependentlyOwned : Bool
    p2IndependentTotalTen : Bool
    p3IndependentTotalTwo : Bool
    integralPBTateObjectSourced : Bool
    finiteLengthDVRBrauerFrameworkSourced : Bool
    sectorwiseLocalizationAuthoritySpecified : Bool
    sectorwiseLocalizationAuthorityInhabited : Bool
    monsterOrderUsedToDefineWeights : Bool
    residualTenTwoUsedToDefineLengths : Bool
    attributionFirewallPreserved : Bool

canonicalPBLocalizedDVRPreferredPaymentCutsetBoundary :
  PBLocalizedDVRPreferredPaymentCutsetBoundary
canonicalPBLocalizedDVRPreferredPaymentCutsetBoundary =
  pb-localized-dvr-preferred-payment-cutset-boundary
    true true true true true true true false false false true
