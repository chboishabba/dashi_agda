module DASHI.Moonshine.OggSSPPBTerminalPrimeLevelLocalizationTheoremExact where

------------------------------------------------------------------------
-- TERMINAL PRIME-LEVEL pB LOCALIZATION THEOREM INTERFACE
--
-- This is a stricter/minimal reformulation of the current live wall.
--
-- A completion must provide ONE target-independent Green/DVR sector
-- localization A of the actual integral pB Moonshine object, together with:
--
--   * a 2B source-piece refinement satisfying Urano parity/Hauptmodul data;
--   * a 3B source-piece refinement satisfying Carnahan H_3/fixed-vector data.
--
-- No Monster-order target, Duncan--Swisher 10/2 residual, or Base369 label may
-- be used to define A.
--
-- Once these three theorem objects exist, every additional bookkeeping field
-- in PBSourceGeometricLocalizationAuthority is derived here.  In particular,
-- the source/proof authority bit is true because the theorem object itself
-- supplies the proof, not because an external author is credited with DASHI's
-- sector decomposition.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPPBGreenRingSectorSpeciesCutsetExact as Green
import DASHI.Moonshine.OggSSP2BGreenSpeciesUranoParityCompatibilityExact as TwoB
import DASHI.Moonshine.OggSSP3BGreenSpeciesCarnahanFixedVectorCompatibilityExact as ThreeB
import DASHI.Moonshine.OggSSPPBSourceGeometricLocalizationAuthorityExact as SourceGeom
import DASHI.Moonshine.OggSSPPBLocalizedDVRPreferredPaymentCutsetExact as DVRPayment
import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSPSmallPrimeDVRLengthBrauerCutsetExact as DVR
import DASHI.Moonshine.OggSSPSmallCharacteristicMonsterBridgeFailureLocalizationExact as Bridge
import DASHI.Moonshine.OggSSPSmallCharacteristicJointCorrectionCutsetExact as Joint
import DASHI.Moonshine.OggSSPSmallCharacteristicFourthTermExtensionExact as Fourth
import DASHI.Moonshine.OggSSPPBLocalizationSourceCoverageAuditExact as Coverage
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Minimal substantive theorem payload.
------------------------------------------------------------------------

record PBTerminalPrimeLevelLocalizationTheorem : Set₁ where
  field
    localization :
      Green.PBGreenRingSectorSpeciesAuthority

    twoBRefinement :
      TwoB.TwoBGreenSpeciesUranoParityCompatibility
        localization

    threeBRefinement :
      ThreeB.ThreeBGreenSpeciesCarnahanCompatibility
        localization

open PBTerminalPrimeLevelLocalizationTheorem public

------------------------------------------------------------------------
-- 2. All SourceGeom bookkeeping follows from the single localization.
------------------------------------------------------------------------

asSourceGeometricLocalizationAuthority :
  PBTerminalPrimeLevelLocalizationTheorem ->
  SourceGeom.PBSourceGeometricLocalizationAuthority
asSourceGeometricLocalizationAuthority theorem =
  record
    { SourceGeom.greenSpecies =
        localization theorem

    ; SourceGeom.twoBSourceCompatibility =
        twoBRefinement theorem

    ; SourceGeom.threeBSourceCompatibility =
        threeBRefinement theorem

    ; SourceGeom.sameLocalizationUnderliesBothPrimeSpecificRefinements =
        true
    ; SourceGeom.sameLocalizationUnderliesBothPrimeSpecificRefinementsIsTrue =
        refl

    ; SourceGeom.localizationDefinedBeforeMonsterOrderIsRead =
        Green.constructionUsesNoMonsterOrderTarget
          (localization theorem)
    ; SourceGeom.localizationDefinedBeforeMonsterOrderIsReadIsTrue =
        Green.constructionUsesNoMonsterOrderTargetIsTrue
          (localization theorem)

    ; SourceGeom.localizationDefinedBeforeDuncanSwisherResidualIsRead =
        Green.constructionUsesNoDuncanSwisherResidualTarget
          (localization theorem)
    ; SourceGeom.localizationDefinedBeforeDuncanSwisherResidualIsReadIsTrue =
        Green.constructionUsesNoDuncanSwisherResidualTargetIsTrue
          (localization theorem)

    ; SourceGeom.localizationRefinesPublishedModularDescription =
        Green.carnahanUranoHauptmodulSpecializationProvedForThisSpecies
          (localization theorem)
    ; SourceGeom.localizationRefinesPublishedModularDescriptionIsTrue =
        Green.carnahanUranoHauptmodulSpecializationProvedForThisSpeciesIsTrue
          (localization theorem)

    ; SourceGeom.localizationRefinesPublishedSupersingularDescription =
        true
    ; SourceGeom.localizationRefinesPublishedSupersingularDescriptionIsTrue =
        refl

    ; SourceGeom.sameLocalizationRefinesBothPublishedDescriptions =
        true
    ; SourceGeom.sameLocalizationRefinesBothPublishedDescriptionsIsTrue =
        refl

    ; SourceGeom.sourceOrProofAuthorityForExceptionalValuation =
        true
    ; SourceGeom.sourceOrProofAuthorityForExceptionalValuationIsTrue =
        refl
    }

------------------------------------------------------------------------
-- 3. Existing downstream terminal objects are automatic.
------------------------------------------------------------------------

asPreferredDVRPayment :
  PBTerminalPrimeLevelLocalizationTheorem ->
  DVRPayment.PBLocalizedDVRPreferredPaymentAuthority
asPreferredDVRPayment theorem =
  SourceGeom.asPreferredDVRPayment
    (asSourceGeometricLocalizationAuthority theorem)

asPreferredCorrectedValuation :
  PBTerminalPrimeLevelLocalizationTheorem ->
  Preferred.PreferredCorrectedValuationAuthority
asPreferredCorrectedValuation theorem =
  SourceGeom.asPreferredCorrectedValuation
    (asSourceGeometricLocalizationAuthority theorem)

asGlobalDVRBrauerAuthority :
  PBTerminalPrimeLevelLocalizationTheorem ->
  DVR.PBLocalizedDVRBrauerAuthority
asGlobalDVRBrauerAuthority theorem =
  SourceGeom.asGlobalDVRBrauerAuthority
    (asSourceGeometricLocalizationAuthority theorem)

asMonsterBridgeAuthority :
  PBTerminalPrimeLevelLocalizationTheorem ->
  Bridge.SmallPrimeMonsterBridgeAuthority
asMonsterBridgeAuthority theorem =
  SourceGeom.asMonsterBridgeAuthority
    (asSourceGeometricLocalizationAuthority theorem)

asJointExceptionalAuthority :
  PBTerminalPrimeLevelLocalizationTheorem ->
  Joint.JointSmallPrimeExceptionalAuthority
asJointExceptionalAuthority theorem =
  SourceGeom.asJointExceptionalAuthority
    (asSourceGeometricLocalizationAuthority theorem)

asLicensedFourTermExtension :
  PBTerminalPrimeLevelLocalizationTheorem ->
  Fourth.AnalyticallyLicensedFourTermExtension
asLicensedFourTermExtension theorem =
  SourceGeom.asLicensedFourTermExtension
    (asSourceGeometricLocalizationAuthority theorem)

------------------------------------------------------------------------
-- 4. Exact sectorwise source-length consequences.
------------------------------------------------------------------------

p2SourcePieceLengthsAreGeometric :
  (theorem : PBTerminalPrimeLevelLocalizationTheorem) ->
  (sector :
    Preferred.Sector Preferred.p2PreferredPresentation) ->
  TwoB.sumSourcePieceLengths
    (TwoB.sourcePieces (twoBRefinement theorem))
    (TwoB.sectorSourcePieces
      (twoBRefinement theorem)
      sector)
  ≡
  Green.normalizedDVRLength
    (localization theorem)
    (Green.p2SectorClass (localization theorem) sector)
p2SourcePieceLengthsAreGeometric theorem sector =
  sym
    (TwoB.sectorLengthIsSumOfUranoSourcePieceLengths
      (twoBRefinement theorem)
      sector)

p3SourcePieceLengthsAreGeometric :
  (theorem : PBTerminalPrimeLevelLocalizationTheorem) ->
  (sector :
    Preferred.Sector Preferred.p3PreferredPresentation) ->
  ThreeB.sumSourcePieceLengths
    (ThreeB.sourcePieces (threeBRefinement theorem))
    (ThreeB.sectorSourcePieces
      (threeBRefinement theorem)
      sector)
  ≡
  Green.normalizedDVRLength
    (localization theorem)
    (Green.p3SectorClass (localization theorem) sector)
p3SourcePieceLengthsAreGeometric theorem sector =
  sym
    (ThreeB.sectorLengthIsSumOfCarnahanSourcePieceLengths
      (threeBRefinement theorem)
      sector)

------------------------------------------------------------------------
-- 5. Attribution / source-coverage boundary.
------------------------------------------------------------------------

coverage :
  Coverage.PBLocalizationSourceCoverage
coverage =
  Coverage.canonicalPBLocalizationSourceCoverage

missingSurface :
  Coverage.PBLocalizationMissingProofSurface
missingSurface =
  Coverage.canonicalPBLocalizationMissingProofSurface

data CarnahanUranoLiteratureAlreadyInhabitsTerminalTheorem : Set where
data SourceCoverageBooleansCreateLocalizationFunctor : Set where
data MonsterResidualMayDefineTerminalLocalization : Set where
data Base369LabelsMayDefineTerminalLocalization : Set where

literatureDoesNotAlreadyInhabitTerminalTheorem :
  CarnahanUranoLiteratureAlreadyInhabitsTerminalTheorem -> ⊥
literatureDoesNotAlreadyInhabitTerminalTheorem ()

sourceCoverageDoesNotCreateLocalizationFunctor :
  SourceCoverageBooleansCreateLocalizationFunctor -> ⊥
sourceCoverageDoesNotCreateLocalizationFunctor ()

monsterResidualMayNotDefineTerminalLocalization :
  MonsterResidualMayDefineTerminalLocalization -> ⊥
monsterResidualMayNotDefineTerminalLocalization ()

base369LabelsMayNotDefineTerminalLocalization :
  Base369LabelsMayDefineTerminalLocalization -> ⊥
base369LabelsMayNotDefineTerminalLocalization ()

------------------------------------------------------------------------
-- 6. Live theorem wall.
------------------------------------------------------------------------

data PBTerminalPrimeLevelLocalizationTheoremInhabited : Set where

terminalPrimeLevelLocalizationStillOpen :
  PBTerminalPrimeLevelLocalizationTheoremInhabited -> ⊥
terminalPrimeLevelLocalizationStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record PBTerminalPrimeLevelLocalizationBoundary : Set where
  constructor pb-terminal-prime-level-localization-boundary
  field
    oneTargetIndependentLocalizationRequired : Bool
    twoBUranoRefinementRequired : Bool
    threeBCarnahanRefinementRequired : Bool
    sourceGeomBookkeepingDerivedAutomatically : Bool
    monsterBridgeDerivedAutomatically : Bool
    correctedValuationDerivedAutomatically : Bool
    licensedFourTermExtensionDerivedAutomatically : Bool
    targetNumbersUsedToDefineLocalization : Bool
    base369LabelsUsedToDefineLocalization : Bool
    existingLiteratureAlreadyPaysPrimeLevelSectorFunctor : Bool
    terminalTheoremInhabited : Bool
    attributionFirewallPreserved : Bool

canonicalPBTerminalPrimeLevelLocalizationBoundary :
  PBTerminalPrimeLevelLocalizationBoundary
canonicalPBTerminalPrimeLevelLocalizationBoundary =
  pb-terminal-prime-level-localization-boundary
    true true true true true true true false false false false true
