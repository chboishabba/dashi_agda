module DASHI.Moonshine.OggSSPP2BanerjeeGaussianCMOrientedInertiaSourceExact where

------------------------------------------------------------------------
-- BANERJEE + GAUSSIAN-CM ORIENTED INERTIA SAME-SOURCE CANDIDATE
--
-- Corrected ten-state source candidate:
--
--   two Gaussian-CM orientations
--     x
--   five G24 / Gal(F4/F2) conjugacy-class orbits
--
-- The five labels are already the Galois quotient of the seven G24
-- conjugacy classes; the Banerjee Galois sheet is therefore NOT reused as an
-- independent binary factor.
--
-- The independent binary marking is the classically sourced orientation
-- doublet of the imaginary quadratic / Gaussian-CM order.
--
-- Remaining source theorem:
--   realize those two CM orientations as normalized optimal embeddings on
--   the SAME Banerjee supersingular endomorphism object, and attach the
--   proof-bearing Gamma_0(4) finite-flat subgroup/subflag.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Product using (_×_; _,_)

import DASHI.Moonshine.OggSSPP2BanerjeeF4UniversalDeformationSourceExact as Banerjee
import DASHI.Moonshine.OggSSPP2BanerjeeF4SameSourceRealizationExact as BanerjeeSource
import DASHI.Moonshine.OggSSPP2BanerjeeGaloisClassOrbitFiveExact as GaloisFive
import DASHI.Moonshine.OggSSPP2OrientedInertiaTenStateRecognitionExact as Ten
import DASHI.Moonshine.OggSSPP2OrientedInertiaUniversalDeformationRealizationExact as Oriented
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Inertia
import DASHI.Moonshine.OggSSPP2Gamma0FourMarkedSubgroupSchemeSourceExact as Gamma
import DASHI.Moonshine.OggSSPP2UniqueGamma0FourMarkingBidiExact as Bidi
import DASHI.Moonshine.OggSSPP2SupersingularUniversalDeformationSourceExact as Universal
import DASHI.Moonshine.OggSSPP2F4FrobeniusCandidateNoGoExact as F4
import DASHI.Moonshine.OggSSPP2F4AntipodalStratifiedRefinementExact as Target
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

State : Set
State =
  Ten.P2OrientedInertiaState

orientationConjugation :
  State ->
  State
orientationConjugation
  (Ten.firstGaloisOrientation , inertia) =
  Ten.conjugateGaloisOrientation , inertia
orientationConjugation
  (Ten.conjugateGaloisOrientation , inertia) =
  Ten.firstGaloisOrientation , inertia

orientationConjugationInvolutive :
  (state : State) ->
  orientationConjugation (orientationConjugation state) ≡ state
orientationConjugationInvolutive
  (Ten.firstGaloisOrientation , inertia) = refl
orientationConjugationInvolutive
  (Ten.conjugateGaloisOrientation , inertia) = refl

coarseOrbit :
  State ->
  F4.F4FrobeniusOrbit
coarseOrbit =
  Oriented.sourceCoarseOrbit

orientationConjugationChangesCentre :
  coarseOrbit
    (orientationConjugation
      (Ten.firstGaloisOrientation , Inertia.identityInertiaOrbit))
  ≡
  coarseOrbit
    (Ten.firstGaloisOrientation , Inertia.identityInertiaOrbit)
  ->
  ⊥
orientationConjugationChangesCentre ()

------------------------------------------------------------------------
-- 1. Source authority and one proof-bearing attachment.
------------------------------------------------------------------------

record BanerjeeGaussianCMSourceAuthority : Set₁ where
  field
    banerjeeAuthority :
      BanerjeeSource.BanerjeeF4SourceAuthority

    universalFamilyState :
      Universal.EllipticFamilyState
        (BanerjeeSource.datum banerjeeAuthority)

    sourceIdentifiesGaussianCMReductionOnThisSupersingularObject :
      Bool

    sourceIdentifiesGaussianCMReductionOnThisSupersingularObjectIsTrue :
      sourceIdentifiesGaussianCMReductionOnThisSupersingularObject ≡ true

open BanerjeeGaussianCMSourceAuthority public

record BanerjeeGaussianCMAttachment
  (authority : BanerjeeGaussianCMSourceAuthority) : Set₁ where
  field
    OrderFourSubgroup : Set
    OrderTwoSubgroup : Set

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

    gaussianCMOrientationRealized :
      Ten.ClassicalQuadraticOrientation ->
      Bool

    gaussianCMOrientationRealizedIsTrue :
      (orientation : Ten.ClassicalQuadraticOrientation) ->
      gaussianCMOrientationRealized orientation ≡ true

    g24GaloisOrbitRealized :
      Inertia.BinaryTetrahedralInversionOrbit ->
      Bool

    g24GaloisOrbitRealizedIsTrue :
      (orbit : Inertia.BinaryTetrahedralInversionOrbit) ->
      g24GaloisOrbitRealized orbit ≡ true

    rawFrobenius :
      State -> State

    rawFrobeniusInvolutive :
      (state : State) ->
      rawFrobenius (rawFrobenius state) ≡ state

    rawFrobeniusPreservesCoarseOrbit :
      (state : State) ->
      coarseOrbit (rawFrobenius state)
      ≡ coarseOrbit state

    rawFrobeniusCommutesWithOrientationConjugation :
      (state : State) ->
      rawFrobenius (orientationConjugation state)
      ≡ orientationConjugation (rawFrobenius state)

    sourceReference :
      String

open BanerjeeGaussianCMAttachment public

------------------------------------------------------------------------
-- 2. Exact finite-flat datum over the SAME Banerjee family state.
------------------------------------------------------------------------

finiteFlatDatum :
  {authority : BanerjeeGaussianCMSourceAuthority} ->
  BanerjeeGaussianCMAttachment authority ->
  Gamma.Gamma0FourFiniteFlatDatum
finiteFlatDatum {authority} attachment =
  record
    { EllipticObject =
        Universal.EllipticFamilyState
          (BanerjeeSource.datum (banerjeeAuthority authority))
    ; OrderFourSubgroup =
        OrderFourSubgroup attachment
    ; OrderTwoSubgroup =
        OrderTwoSubgroup attachment
    ; selectedEllipticObject =
        universalFamilyState authority
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

------------------------------------------------------------------------
-- 3. Marking and exact ten-state bidi.
------------------------------------------------------------------------

marking :
  {authority : BanerjeeGaussianCMSourceAuthority} ->
  (attachment : BanerjeeGaussianCMAttachment authority) ->
  Universal.Gamma0FourUniversalDeformationMarking
    (BanerjeeSource.datum (banerjeeAuthority authority))
marking {authority} attachment =
  record
    { MarkedState =
        State
    ; underlyingFamilyState =
        λ _ -> universalFamilyState authority
    ; specializesToRawSubgroup =
        λ _ -> BanerjeeSource.Unique.kerFrobeniusSquared
    ; specializationIsUniqueKerFrobeniusSquared =
        λ _ -> refl
    ; gamma0FourLevelStructurePresent =
        λ _ -> gammaZeroLevelFourSemantics attachment
    ; gamma0FourLevelStructurePresentIsTrue =
        λ _ -> gammaZeroLevelFourSemanticsIsTrue attachment
    ; deformationProvenanceRetained =
        λ state ->
          gaussianCMOrientationRealized attachment (Data.Product.proj₁ state)
    ; deformationProvenanceRetainedIsTrue =
        λ state ->
          gaussianCMOrientationRealizedIsTrue attachment
            (Data.Product.proj₁ state)
    }

markingBidi :
  {authority : BanerjeeGaussianCMSourceAuthority} ->
  (attachment : BanerjeeGaussianCMAttachment authority) ->
  Bidi.UniqueGamma0FourMarkingBidi
    (Universal.toUniqueSubgroupMarking (marking attachment))
markingBidi attachment =
  record
    { sourceCoarseOrbit =
        coarseOrbit
    ; toTarget =
        Oriented.toTarget
    ; fromTarget =
        Oriented.fromTarget
    ; sourceRoundTrip =
        Oriented.sourceRoundTrip
    ; targetRoundTrip =
        Oriented.targetRoundTrip
    ; toTargetPreservesCoarseOrbit =
        λ state -> refl
    ; fromTargetPreservesCoarseOrbit =
        λ state -> cong Target.stratumOf (Oriented.targetRoundTrip state)
    ; everyMappedStateStillLiesOverUniqueRawSubgroup =
        λ state -> refl
    }

tenStateRecognition :
  {authority : BanerjeeGaussianCMSourceAuthority} ->
  (attachment : BanerjeeGaussianCMAttachment authority) ->
  Universal.UniversalDeformationTenStateRecognition
    (BanerjeeSource.datum (banerjeeAuthority authority))
    (marking attachment)
tenStateRecognition attachment =
  record
    { arithmeticBidi =
        markingBidi attachment
    }

rawFrobeniusSource :
  {authority : BanerjeeGaussianCMSourceAuthority} ->
  (attachment : BanerjeeGaussianCMAttachment authority) ->
  Gamma.Gamma0FourMarkedArithmeticSource
rawFrobeniusSource attachment =
  record
    { datum =
        finiteFlatDatum attachment
    ; MarkedState =
        State
    ; frobenius =
        rawFrobenius attachment
    ; frobeniusInvolutive =
        rawFrobeniusInvolutive attachment
    ; coarseF4Orbit =
        coarseOrbit
    ; coarseF4OrbitInvariant =
        rawFrobeniusPreservesCoarseOrbit attachment
    }

------------------------------------------------------------------------
-- 4. Corrected frontier.
------------------------------------------------------------------------

data BanerjeeGaussianCMResidual : Set where
  missingBanerjeeSourceSemanticAuthority :
    BanerjeeGaussianCMResidual

  missingGaussianCMOrientationRealizationOnBanerjeeObject :
    BanerjeeGaussianCMResidual

  missingFiniteFlatGamma0FourAttachment :
    BanerjeeGaussianCMResidual

  missingRawFrobeniusCompatibility :
    BanerjeeGaussianCMResidual

firstResidual :
  BanerjeeGaussianCMResidual
firstResidual =
  missingBanerjeeSourceSemanticAuthority

data BanerjeeGaloisSheetIsIndependentOrientationFactor : Set where

banerjeeGaloisSheetDoesNotBecomeIndependentOrientationFactor :
  BanerjeeGaloisSheetIsIndependentOrientationFactor -> ⊥
banerjeeGaloisSheetDoesNotBecomeIndependentOrientationFactor ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record BanerjeeGaussianCMOrientedInertiaBoundary : Set where
  constructor banerjee-gaussian-cm-oriented-inertia-boundary
  field
    banerjeeF4UniversalSourceReused : Bool
    fiveInertiaLabelsAlreadyGaloisQuotient : Bool
    independentBinaryFactorIsCMOrientation : Bool
    banerjeeGaloisSheetUsedAsIndependentBinaryFactor : Bool
    proofBearingCMOrientationRealizationRequired : Bool
    proofBearingGamma0FourAttachmentRequired : Bool
    oneAttachmentConstructsTenStateBidi : Bool
    namedClassicalTenStateModuliObjectClaimed : Bool

canonicalBanerjeeGaussianCMOrientedInertiaBoundary :
  BanerjeeGaussianCMOrientedInertiaBoundary
canonicalBanerjeeGaussianCMOrientedInertiaBoundary =
  banerjee-gaussian-cm-oriented-inertia-boundary
    true true true false true true true false
