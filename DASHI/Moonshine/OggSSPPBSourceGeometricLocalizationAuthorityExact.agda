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
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as P2Sector
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact as P3Sector
import DASHI.Moonshine.OggSSPSmallCharacteristicMonsterBridgeFailureLocalizationExact as Bridge
import DASHI.Moonshine.OggSSPSmallCharacteristicJointCorrectionCutsetExact as Joint
import DASHI.Moonshine.OggSSPSmallCharacteristicFourthTermExtensionExact as Fourth

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

    localizationRefinesPublishedModularDescription :
      Bool
    localizationRefinesPublishedModularDescriptionIsTrue :
      localizationRefinesPublishedModularDescription ≡ true

    localizationRefinesPublishedSupersingularDescription :
      Bool
    localizationRefinesPublishedSupersingularDescriptionIsTrue :
      localizationRefinesPublishedSupersingularDescription ≡ true

    sameLocalizationRefinesBothPublishedDescriptions :
      Bool
    sameLocalizationRefinesBothPublishedDescriptionsIsTrue :
      sameLocalizationRefinesBothPublishedDescriptions ≡ true

    sourceOrProofAuthorityForExceptionalValuation :
      Bool
    sourceOrProofAuthorityForExceptionalValuationIsTrue :
      sourceOrProofAuthorityForExceptionalValuation ≡ true

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
-- 2b. Exact source-piece partition equations forced by a joint localization.
------------------------------------------------------------------------

p2UranoPieceLengthSumIsGeometricDepth :
  (A : PBSourceGeometricLocalizationAuthority) ->
  (sector : Preferred.Sector Preferred.p2PreferredPresentation) ->
  TwoB.sumSourcePieceLengths
    (TwoB.sourcePieces (twoBSourceCompatibility A))
    (TwoB.sectorSourcePieces
      (twoBSourceCompatibility A)
      sector)
  ≡
  P2Geom.sectorIsotropyDenominatorTwoAdicDepth sector
p2UranoPieceLengthSumIsGeometricDepth A sector =
  trans
    (sym
      (TwoB.sectorLengthIsSumOfUranoSourcePieceLengths
        (twoBSourceCompatibility A)
        sector))
    (p2LocalizedLengthIsStackIsotropyDepth A sector)

p3CarnahanPieceLengthSumIsSemistableMultiplicity :
  (A : PBSourceGeometricLocalizationAuthority) ->
  (sector : Preferred.Sector Preferred.p3PreferredPresentation) ->
  ThreeB.sumSourcePieceLengths
    (ThreeB.sourcePieces (threeBSourceCompatibility A))
    (ThreeB.sectorSourcePieces
      (threeBSourceCompatibility A)
      sector)
  ≡
  P3Geom.p3LocalGeometricMultiplicity sector
p3CarnahanPieceLengthSumIsSemistableMultiplicity A sector =
  trans
    (sym
      (ThreeB.sectorLengthIsSumOfCarnahanSourcePieceLengths
        (threeBSourceCompatibility A)
        sector))
    (p3LocalizedLengthIsSemistableMultiplicity A sector)

p2IdentitySectorSourceLengthIsThree :
  (A : PBSourceGeometricLocalizationAuthority) ->
  TwoB.sumSourcePieceLengths
    (TwoB.sourcePieces (twoBSourceCompatibility A))
    (TwoB.sectorSourcePieces
      (twoBSourceCompatibility A)
      P2Sector.identityInertiaOrbit)
  ≡ 3
p2IdentitySectorSourceLengthIsThree A =
  p2UranoPieceLengthSumIsGeometricDepth
    A
    P2Sector.identityInertiaOrbit

p2MinusOneSectorSourceLengthIsThree :
  (A : PBSourceGeometricLocalizationAuthority) ->
  TwoB.sumSourcePieceLengths
    (TwoB.sourcePieces (twoBSourceCompatibility A))
    (TwoB.sectorSourcePieces
      (twoBSourceCompatibility A)
      P2Sector.centralMinusOneInertiaOrbit)
  ≡ 3
p2MinusOneSectorSourceLengthIsThree A =
  p2UranoPieceLengthSumIsGeometricDepth
    A
    P2Sector.centralMinusOneInertiaOrbit

p2OrderFourSectorSourceLengthIsTwo :
  (A : PBSourceGeometricLocalizationAuthority) ->
  TwoB.sumSourcePieceLengths
    (TwoB.sourcePieces (twoBSourceCompatibility A))
    (TwoB.sectorSourcePieces
      (twoBSourceCompatibility A)
      P2Sector.orderFourInertiaOrbit)
  ≡ 2
p2OrderFourSectorSourceLengthIsTwo A =
  p2UranoPieceLengthSumIsGeometricDepth
    A
    P2Sector.orderFourInertiaOrbit

p2OrderThreeSectorSourceLengthIsOne :
  (A : PBSourceGeometricLocalizationAuthority) ->
  TwoB.sumSourcePieceLengths
    (TwoB.sourcePieces (twoBSourceCompatibility A))
    (TwoB.sectorSourcePieces
      (twoBSourceCompatibility A)
      P2Sector.orderThreePairInertiaOrbit)
  ≡ 1
p2OrderThreeSectorSourceLengthIsOne A =
  p2UranoPieceLengthSumIsGeometricDepth
    A
    P2Sector.orderThreePairInertiaOrbit

p2OrderSixSectorSourceLengthIsOne :
  (A : PBSourceGeometricLocalizationAuthority) ->
  TwoB.sumSourcePieceLengths
    (TwoB.sourcePieces (twoBSourceCompatibility A))
    (TwoB.sectorSourcePieces
      (twoBSourceCompatibility A)
      P2Sector.orderSixPairInertiaOrbit)
  ≡ 1
p2OrderSixSectorSourceLengthIsOne A =
  p2UranoPieceLengthSumIsGeometricDepth
    A
    P2Sector.orderSixPairInertiaOrbit

p3NodeSectorSourceLengthIsOne :
  (A : PBSourceGeometricLocalizationAuthority) ->
  ThreeB.sumSourcePieceLengths
    (ThreeB.sourcePieces (threeBSourceCompatibility A))
    (ThreeB.sectorSourcePieces
      (threeBSourceCompatibility A)
      P3Sector.nodeOrbit)
  ≡ 1
p3NodeSectorSourceLengthIsOne A =
  p3CarnahanPieceLengthSumIsSemistableMultiplicity
    A
    P3Sector.nodeOrbit

p3BranchSectorSourceLengthIsOne :
  (A : PBSourceGeometricLocalizationAuthority) ->
  ThreeB.sumSourcePieceLengths
    (ThreeB.sourcePieces (threeBSourceCompatibility A))
    (ThreeB.sectorSourcePieces
      (threeBSourceCompatibility A)
      P3Sector.branchOrbit)
  ≡ 1
p3BranchSectorSourceLengthIsOne A =
  p3CarnahanPieceLengthSumIsSemistableMultiplicity
    A
    P3Sector.branchOrbit

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
-- 3b. Direct adapter to the existing Monster bridge.
--
-- The exceptional object is the combined localized DVR module itself.  Its
-- valuation is normalized composition length.  The 10/2 equations are derived
-- from sectorwise lengths and additivity; they are not used to define the
-- localization.
------------------------------------------------------------------------

asMonsterBridgeAuthority :
  PBSourceGeometricLocalizationAuthority ->
  Bridge.SmallPrimeMonsterBridgeAuthority
asMonsterBridgeAuthority A =
  record
    { Bridge.ExceptionalObject =
        Green.ModuleClass (Green.species (greenSpecies A))
    ; Bridge.p2ExceptionalObject =
        Green.p2CombinedLocalizedClass (greenSpecies A)
    ; Bridge.p3ExceptionalObject =
        Green.p3CombinedLocalizedClass (greenSpecies A)
    ; Bridge.exceptionalValuation =
        λ prime moduleClass ->
          Green.normalizedDVRLength (greenSpecies A) moduleClass
    ; Bridge.p2ExceptionalValuationIsBridgeGap =
        Green.p2CombinedLengthIsTen (greenSpecies A)
    ; Bridge.p3ExceptionalValuationIsBridgeGap =
        Green.p3CombinedLengthIsTwo (greenSpecies A)
    ; Bridge.objectDefinedIndependentlyOfMonsterTarget =
        localizationDefinedBeforeMonsterOrderIsRead A
    ; Bridge.objectDefinedIndependentlyOfMonsterTargetIsTrue =
        localizationDefinedBeforeMonsterOrderIsReadIsTrue A
    ; Bridge.refinesModularDescription =
        localizationRefinesPublishedModularDescription A
    ; Bridge.refinesModularDescriptionIsTrue =
        localizationRefinesPublishedModularDescriptionIsTrue A
    ; Bridge.refinesSupersingularDescription =
        localizationRefinesPublishedSupersingularDescription A
    ; Bridge.refinesSupersingularDescriptionIsTrue =
        localizationRefinesPublishedSupersingularDescriptionIsTrue A
    ; Bridge.sameObjectRefinesBothDescriptions =
        sameLocalizationRefinesBothPublishedDescriptions A
    ; Bridge.sameObjectRefinesBothDescriptionsIsTrue =
        sameLocalizationRefinesBothPublishedDescriptionsIsTrue A
    ; Bridge.sourceOrProofAuthorityForExceptionalValuation =
        sourceOrProofAuthorityForExceptionalValuation A
    ; Bridge.sourceOrProofAuthorityForExceptionalValuationIsTrue =
        sourceOrProofAuthorityForExceptionalValuationIsTrue A
    }

asJointExceptionalAuthority :
  PBSourceGeometricLocalizationAuthority ->
  Joint.JointSmallPrimeExceptionalAuthority
asJointExceptionalAuthority A =
  Bridge.asJointAuthority (asMonsterBridgeAuthority A)

asLicensedFourTermExtension :
  PBSourceGeometricLocalizationAuthority ->
  Fourth.AnalyticallyLicensedFourTermExtension
asLicensedFourTermExtension A =
  Joint.asFourTermExtension (asJointExceptionalAuthority A)

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
    sourcePiecePartitionLengthEquationsDerived : Bool
    explicitP2ThreeThreeTwoOneOneSourceSumsDerived : Bool
    explicitP3OneOneSourceSumsDerived : Bool
    preferredDVRAdapterOwned : Bool
    preferredCorrectedValuationAdapterOwned : Bool
    globalDVRBrauerAdapterOwned : Bool
    directMonsterBridgeAdapterOwned : Bool
    jointExceptionalAdapterOwned : Bool
    licensedFourTermAdapterOwned : Bool
    sameObjectRefinementRequired : Bool
    jointAuthorityInhabited : Bool
    targetNumbersUsedToDefineAuthority : Bool
    attributionFirewallPreserved : Bool

canonicalPBSourceGeometricLocalizationBoundary :
  PBSourceGeometricLocalizationBoundary
canonicalPBSourceGeometricLocalizationBoundary =
  pb-source-geometric-localization-boundary
    true true true true true true true true true true true true true true true true false false true
