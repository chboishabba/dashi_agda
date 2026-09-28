module DASHI.Moonshine.OggSSPPBSourceGeometricLocalizationAuthorityExact where

------------------------------------------------------------------------
-- TERMINAL pB SOURCE/GEOMETRIC LOCALIZATION AUTHORITY
--
-- This is the smallest current joint theorem target.
--
-- A legitimate completion must construct ONE target-independent localization
-- of the actual integral pB Moonshine object which simultaneously:
--
--   * carries the Green-ring / finite-DVR sector species;
--   * reopens every p=2 inertia sector through Urano-compatible graded 2B
--     source pieces;
--   * reopens every p=3 Deligne--Rapoport sector through Carnahan H_3
--     source pieces embedded equivariantly in 3B-fixed vectors;
--   * has normalized DVR composition lengths equal to the independently
--     grounded geometric local quantities:
--
--         p=2 : v_2 of inertia-sector isotropy denominator,
--         p=3 : Deligne--Rapoport semistable local multiplicity.
--
-- Once this authority exists, all existing preferred/global DVR and corrected
-- Hauptmodul payment interfaces are obtained by adapters.  No Monster-order
-- target or Duncan--Swisher 10/2 residual may be used to define it.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPPBGreenRingSectorSpeciesCutsetExact as Green
import DASHI.Moonshine.OggSSP2BGreenSpeciesUranoParityCompatibilityExact as TwoB
import DASHI.Moonshine.OggSSP3BGreenSpeciesCarnahanFixedVectorCompatibilityExact as ThreeB
import DASHI.Moonshine.OggSSPPBLocalizedDVRPreferredPaymentCutsetExact as DVRPayment
import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSPSmallPrimeDVRLengthBrauerCutsetExact as DVR
import DASHI.Moonshine.OggSSPP2InertiaStackDenominatorValuationExact as P2Geom
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalMultiplicityExact as P3Geom
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. One joint authority.
------------------------------------------------------------------------

record PBSourceGeometricLocalizationAuthority : Set₁ where
  field
    greenSpecies :
      Green.PBGreenRingSectorSpeciesAuthority

    twoBSourceCompatibility :
      TwoB.TwoBGreenSpeciesUranoParityCompatibility
        greenSpecies

    threeBSourceCompatibility :
      ThreeB.ThreeBGreenSpeciesCarnahanCompatibility
        greenSpecies

    sameLocalizationUnderliesBothPrimeSpecificRefinements :
      Bool
    sameLocalizationUnderliesBothPrimeSpecificRefinementsIsTrue :
      sameLocalizationUnderliesBothPrimeSpecificRefinements ≡ true

    localizationDefinedBeforeMonsterOrderIsRead :
      Bool
    localizationDefinedBeforeMonsterOrderIsReadIsTrue :
      localizationDefinedBeforeMonsterOrderIsRead ≡ true

    localizationDefinedBeforeDuncanSwisherResidualIsRead :
      Bool
    localizationDefinedBeforeDuncanSwisherResidualIsReadIsTrue :
      localizationDefinedBeforeDuncanSwisherResidualIsRead ≡ true

open PBSourceGeometricLocalizationAuthority public

------------------------------------------------------------------------
-- 2. Derived geometric length laws.
------------------------------------------------------------------------

p2LocalizedLengthIsStackIsotropyDepth :
  (A : PBSourceGeometricLocalizationAuthority) ->
  (sector :
    Preferred.Sector Preferred.p2PreferredPresentation) ->
  Green.normalizedDVRLength
    (greenSpecies A)
    (Green.p2SectorClass (greenSpecies A) sector)
  ≡
  P2Geom.sectorIsotropyDenominatorTwoAdicDepth sector
p2LocalizedLengthIsStackIsotropyDepth A =
  Green.p2LengthMatchesStackIsotropyDenominatorDepth
    (greenSpecies A)

p3LocalizedLengthIsSemistableMultiplicity :
  (A : PBSourceGeometricLocalizationAuthority) ->
  (sector :
    Preferred.Sector Preferred.p3PreferredPresentation) ->
  Green.normalizedDVRLength
    (greenSpecies A)
    (Green.p3SectorClass (greenSpecies A) sector)
  ≡
  P3Geom.p3LocalGeometricMultiplicity sector
p3LocalizedLengthIsSemistableMultiplicity A =
  Green.p3LengthMatchesSemistableLocalMultiplicity
    (greenSpecies A)

------------------------------------------------------------------------
-- 3. Downstream adapters.
------------------------------------------------------------------------

asPreferredDVRPayment :
  PBSourceGeometricLocalizationAuthority ->
  DVRPayment.PBLocalizedDVRPreferredPaymentAuthority
asPreferredDVRPayment A =
  Green.asLocalizedDVRPreferredPaymentAuthority
    (greenSpecies A)

asPreferredCorrectedValuation :
  PBSourceGeometricLocalizationAuthority ->
  Preferred.PreferredCorrectedValuationAuthority
asPreferredCorrectedValuation A =
  Green.asPreferredCorrectedValuationAuthority
    (greenSpecies A)

asGlobalDVRBrauerAuthority :
  PBSourceGeometricLocalizationAuthority ->
  DVR.PBLocalizedDVRBrauerAuthority
asGlobalDVRBrauerAuthority A =
  Green.asGlobalLocalizedDVRBrauerAuthority
    (greenSpecies A)

------------------------------------------------------------------------
-- 4. Source compatibility is retained downstream.
------------------------------------------------------------------------

twoBCompatibilityReceipt :
  (A : PBSourceGeometricLocalizationAuthority) ->
  TwoB.TwoBGreenSpeciesUranoParityCompatibility
    (greenSpecies A)
twoBCompatibilityReceipt =
  twoBSourceCompatibility

threeBCompatibilityReceipt :
  (A : PBSourceGeometricLocalizationAuthority) ->
  ThreeB.ThreeBGreenSpeciesCarnahanCompatibility
    (greenSpecies A)
threeBCompatibilityReceipt =
  threeBSourceCompatibility

------------------------------------------------------------------------
-- 5. No partial-payment shortcut.
------------------------------------------------------------------------

data GreenSpeciesAloneCreatesJointAuthority : Set where
data TwoBCompatibilityAloneCreatesJointAuthority : Set where
data ThreeBCompatibilityAloneCreatesJointAuthority : Set where
data GeometricLengthEqualitiesCreateSourceRefinement : Set where
data SourceRefinementsCreateHauptmodulSpecies : Set where

greenSpeciesAloneDoesNotCreateJointAuthority :
  GreenSpeciesAloneCreatesJointAuthority -> ⊥
greenSpeciesAloneDoesNotCreateJointAuthority ()

twoBCompatibilityAloneDoesNotCreateJointAuthority :
  TwoBCompatibilityAloneCreatesJointAuthority -> ⊥
twoBCompatibilityAloneDoesNotCreateJointAuthority ()

threeBCompatibilityAloneDoesNotCreateJointAuthority :
  ThreeBCompatibilityAloneCreatesJointAuthority -> ⊥
threeBCompatibilityAloneDoesNotCreateJointAuthority ()

geometricLengthsDoNotCreateSourceRefinement :
  GeometricLengthEqualitiesCreateSourceRefinement -> ⊥
geometricLengthsDoNotCreateSourceRefinement ()

sourceRefinementsDoNotCreateHauptmodulSpecies :
  SourceRefinementsCreateHauptmodulSpecies -> ⊥
sourceRefinementsDoNotCreateHauptmodulSpecies ()

------------------------------------------------------------------------
-- 6. Live theorem wall.
------------------------------------------------------------------------

data PBSourceGeometricLocalizationAuthorityInhabited : Set where

pbSourceGeometricLocalizationStillOpen :
  PBSourceGeometricLocalizationAuthorityInhabited -> ⊥
pbSourceGeometricLocalizationStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record PBSourceGeometricLocalizationBoundary : Set where
  constructor pb-source-geometric-localization-boundary
  field
    greenSpeciesAuthorityRequired : Bool
    twoBUranoSourceCompatibilityRequired : Bool
    threeBCarnahanSourceCompatibilityRequired : Bool
    sameLocalizationAcrossRequirementsRequired : Bool
    p2GeometricLengthLawDerived : Bool
    p3GeometricLengthLawDerived : Bool
    preferredDVRAdapterOwned : Bool
    preferredCorrectedValuationAdapterOwned : Bool
    globalDVRBrauerAdapterOwned : Bool
    jointAuthorityInhabited : Bool
    targetNumbersUsedToDefineAuthority : Bool
    attributionFirewallPreserved : Bool

canonicalPBSourceGeometricLocalizationBoundary :
  PBSourceGeometricLocalizationBoundary
canonicalPBSourceGeometricLocalizationBoundary =
  pb-source-geometric-localization-boundary
    true true true true true true true true true false false true
