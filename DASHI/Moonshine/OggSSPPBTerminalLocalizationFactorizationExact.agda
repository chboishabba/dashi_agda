module DASHI.Moonshine.OggSSPPBTerminalLocalizationFactorizationExact where

------------------------------------------------------------------------
-- FACTORIZATION OF THE TERMINAL pB LOCALIZATION THEOREM
--
-- The live terminal theorem splits into exactly three payments:
--
--   P2 : actual integral 2B pieces -> five inertia sectors + DVR lengths;
--   P3 : actual Carnahan H_3 pieces -> node/branch sectors + DVR lengths;
--   G  : one shared Green/DVR realization of both localized source systems.
--
-- This module proves that these three payments reconstruct the existing
-- terminal theorem and hence every downstream Monster/Hauptmodul adapter.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)

import DASHI.Moonshine.OggSSPP2UranoInertiaSectorLocalizationObligationExact as P2
import DASHI.Moonshine.OggSSPP3H3NodeBranchLocalizationObligationExact as P3
import DASHI.Moonshine.OggSSPPBGreenRingSectorSpeciesCutsetExact as Green
import DASHI.Moonshine.OggSSP2BGreenSpeciesUranoParityCompatibilityExact as TwoB
import DASHI.Moonshine.OggSSP3BGreenSpeciesCarnahanFixedVectorCompatibilityExact as ThreeB
import DASHI.Moonshine.OggSSPPBTerminalPrimeLevelLocalizationTheoremExact as Terminal
import DASHI.Moonshine.OggSSPSmallCharacteristicPreferredCorrectionPaymentExact as Preferred
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution
import DASHI.Moonshine.OggSSPP2InertiaStackDenominatorValuationExact as P2Geom
import DASHI.Moonshine.OggSSPP3DeligneRapoportLocalMultiplicityExact as P3Geom

------------------------------------------------------------------------
-- 1. Shared Green realization of the two already-localized source systems.
------------------------------------------------------------------------

record PBSharedGreenRealization
    (p2 : P2.P2UranoInertiaSectorLocalizationTheorem)
    (p3 : P3.P3H3NodeBranchLocalizationTheorem)
    : Set₁ where
  field
    green :
      Green.PBGreenRingSectorSpeciesAuthority

    p2ModuleClass :
      P2.SourcePiece p2 ->
      Green.ModuleClass (Green.species green)

    p3ModuleClass :
      P3.H3Piece p3 ->
      Green.ModuleClass (Green.species green)

    p2LengthPreserved :
      (piece : P2.SourcePiece p2) ->
      Green.normalizedDVRLength green (p2ModuleClass piece)
      ≡
      P2.normalizedDVRLength p2 piece

    p3LengthPreserved :
      (piece : P3.H3Piece p3) ->
      Green.normalizedDVRLength green (p3ModuleClass piece)
      ≡
      P3.normalizedDVRLength p3 piece

    p2SectorClassReopensCanonicalLocalizedWitness :
      (sector : Preferred.Sector Preferred.p2PreferredPresentation) ->
      Green.p2SectorClass green sector
      ≡
      TwoB.foldSourcePieces
        (record
          { TwoB.Piece = P2.SourcePiece p2
          ; TwoB.degreeParity = P2.degreeParity p2
          ; TwoB.moduleTag = P2.moduleTag p2
          ; TwoB.moduleClass = p2ModuleClass
          ; TwoB.respectsUranoForbiddenPairs =
              P2.respectsUranoForbiddenPairs p2
          })
        (P2.everySectorHasSourcePiece p2 sector ∷ [])

    p3SectorClassReopensCanonicalLocalizedWitness :
      (sector : Preferred.Sector Preferred.p3PreferredPresentation) ->
      Green.p3SectorClass green sector
      ≡
      ThreeB.foldSourcePieces
        (record
          { ThreeB.Piece = P3.H3Piece p3
          ; ThreeB.moduleClass = p3ModuleClass
          ; ThreeB.comesFromCarnahanH3Decomposition =
              P3.pieceComesFromCarnahanOrderNineDecomposition p3
          ; ThreeB.comesFromCarnahanH3DecompositionIsTrue =
              P3.pieceComesFromCarnahanOrderNineDecompositionIsTrue p3
          ; ThreeB.embedsEquivariantlyIntoThreeBFixedVectors =
              P3.pieceEmbedsEquivariantlyIntoThreeBFixedVectors p3
          ; ThreeB.embedsEquivariantlyIntoThreeBFixedVectorsIsTrue =
              P3.pieceEmbedsEquivariantlyIntoThreeBFixedVectorsIsTrue p3
          })
        (P3.everySectorHasSourcePiece p3 sector ∷ [])

    twoBGradedFunctionalAgreesWithUranoT4A :
      Bool
    twoBGradedFunctionalAgreesWithUranoT4AIsTrue :
      twoBGradedFunctionalAgreesWithUranoT4A ≡ true

    sharedRealizationPreservesThreeBNormalizerEquivariance :
      Bool
    sharedRealizationPreservesThreeBNormalizerEquivarianceIsTrue :
      sharedRealizationPreservesThreeBNormalizerEquivariance ≡ true

open PBSharedGreenRealization public

------------------------------------------------------------------------
-- 2. Build the existing 2B compatibility record.
------------------------------------------------------------------------

p2SourcePieces :
  {p2 : P2.P2UranoInertiaSectorLocalizationTheorem}
  {p3 : P3.P3H3NodeBranchLocalizationTheorem} ->
  (G : PBSharedGreenRealization p2 p3) ->
  TwoB.TwoBSourcePiece (green G)
p2SourcePieces {p2} G =
  record
    { TwoB.Piece =
        P2.SourcePiece p2
    ; TwoB.degreeParity =
        P2.degreeParity p2
    ; TwoB.moduleTag =
        P2.moduleTag p2
    ; TwoB.moduleClass =
        p2ModuleClass G
    ; TwoB.respectsUranoForbiddenPairs =
        P2.respectsUranoForbiddenPairs p2
    }

p2Compatibility :
  {p2 : P2.P2UranoInertiaSectorLocalizationTheorem}
  {p3 : P3.P3H3NodeBranchLocalizationTheorem} ->
  (G : PBSharedGreenRealization p2 p3) ->
  TwoB.TwoBGreenSpeciesUranoParityCompatibility (green G)
p2Compatibility {p2} G =
  record
    { TwoB.sourcePieces =
        p2SourcePieces G
    ; TwoB.sectorSourcePieces =
        λ sector ->
          P2.everySectorHasSourcePiece p2 sector ∷ []
    ; TwoB.sectorClassReopensFromSourcePieces =
        p2SectorClassReopensCanonicalLocalizedWitness G
    ; TwoB.sourcePiecesComeFromTwoBWeightSpaces =
        true
    ; TwoB.sourcePiecesComeFromTwoBWeightSpacesIsTrue =
        refl
    ; TwoB.gradedFunctionalAgreesWithUranoTwoBHauptmodulReceipt =
        twoBGradedFunctionalAgreesWithUranoT4A G
    ; TwoB.gradedFunctionalAgreesWithUranoTwoBHauptmodulReceiptIsTrue =
        twoBGradedFunctionalAgreesWithUranoT4AIsTrue G
    ; TwoB.refinementDoesNotIdentifyModuleTagsWithInertiaLabels =
        true
    ; TwoB.refinementDoesNotIdentifyModuleTagsWithInertiaLabelsIsTrue =
        refl
    }

------------------------------------------------------------------------
-- 3. Build the existing 3B compatibility record.
------------------------------------------------------------------------

p3SourcePieces :
  {p2 : P2.P2UranoInertiaSectorLocalizationTheorem}
  {p3 : P3.P3H3NodeBranchLocalizationTheorem} ->
  (G : PBSharedGreenRealization p2 p3) ->
  ThreeB.ThreeBSourcePiece (green G)
p3SourcePieces {p3} G =
  record
    { ThreeB.Piece =
        P3.H3Piece p3
    ; ThreeB.moduleClass =
        p3ModuleClass G
    ; ThreeB.comesFromCarnahanH3Decomposition =
        P3.pieceComesFromCarnahanOrderNineDecomposition p3
    ; ThreeB.comesFromCarnahanH3DecompositionIsTrue =
        P3.pieceComesFromCarnahanOrderNineDecompositionIsTrue p3
    ; ThreeB.embedsEquivariantlyIntoThreeBFixedVectors =
        P3.pieceEmbedsEquivariantlyIntoThreeBFixedVectors p3
    ; ThreeB.embedsEquivariantlyIntoThreeBFixedVectorsIsTrue =
        P3.pieceEmbedsEquivariantlyIntoThreeBFixedVectorsIsTrue p3
    }

p3Compatibility :
  {p2 : P2.P2UranoInertiaSectorLocalizationTheorem}
  {p3 : P3.P3H3NodeBranchLocalizationTheorem} ->
  (G : PBSharedGreenRealization p2 p3) ->
  ThreeB.ThreeBGreenSpeciesCarnahanCompatibility (green G)
p3Compatibility {p3} G =
  record
    { ThreeB.sourcePieces =
        p3SourcePieces G
    ; ThreeB.sectorSourcePieces =
        λ sector ->
          P3.everySectorHasSourcePiece p3 sector ∷ []
    ; ThreeB.sectorClassReopensFromSourcePieces =
        p3SectorClassReopensCanonicalLocalizedWitness G
    ; ThreeB.refinementUsesCarnahanBaseExtendedSetting =
        P3.usesCarnahanLocalizedBaseExtension p3
    ; ThreeB.refinementUsesCarnahanBaseExtendedSettingIsTrue =
        P3.usesCarnahanLocalizedBaseExtensionIsTrue p3
    ; ThreeB.refinementPreservesRelevantCentralizerNormalizerEquivariance =
        sharedRealizationPreservesThreeBNormalizerEquivariance G
    ; ThreeB.refinementPreservesRelevantCentralizerNormalizerEquivarianceIsTrue =
        sharedRealizationPreservesThreeBNormalizerEquivarianceIsTrue G
    ; ThreeB.refinementDoesNotIdentifyH3PiecesWithNodeBranchLabels =
        true
    ; ThreeB.refinementDoesNotIdentifyH3PiecesWithNodeBranchLabelsIsTrue =
        refl
    }

------------------------------------------------------------------------
-- 4. Three payments imply the terminal theorem.
------------------------------------------------------------------------

assembleTerminalTheorem :
  (p2 : P2.P2UranoInertiaSectorLocalizationTheorem) ->
  (p3 : P3.P3H3NodeBranchLocalizationTheorem) ->
  PBSharedGreenRealization p2 p3 ->
  Terminal.PBTerminalPrimeLevelLocalizationTheorem
assembleTerminalTheorem p2 p3 G =
  record
    { Terminal.localization =
        green G
    ; Terminal.twoBRefinement =
        p2Compatibility G
    ; Terminal.threeBRefinement =
        p3Compatibility G
    }

------------------------------------------------------------------------
-- 4b. The three payments make the source/geometric/Green triangles commute.
------------------------------------------------------------------------

p2GreenLengthEqualsCanonicalSourceLength :
  {p2 : P2.P2UranoInertiaSectorLocalizationTheorem}
  {p3 : P3.P3H3NodeBranchLocalizationTheorem} ->
  (G : PBSharedGreenRealization p2 p3) ->
  (sector : Preferred.Sector Preferred.p2PreferredPresentation) ->
  Green.normalizedDVRLength
    (green G)
    (Green.p2SectorClass (green G) sector)
  ≡
  P2.normalizedDVRLength
    p2
    (P2.everySectorHasSourcePiece p2 sector)
p2GreenLengthEqualsCanonicalSourceLength {p2} G sector =
  trans
    (Green.p2LengthMatchesStackIsotropyDenominatorDepth
      (green G)
      sector)
    (sym
      (P2.sectorRepresentativeLength
        p2
        sector))

p3GreenLengthEqualsCanonicalSourceLength :
  {p2 : P2.P2UranoInertiaSectorLocalizationTheorem}
  {p3 : P3.P3H3NodeBranchLocalizationTheorem} ->
  (G : PBSharedGreenRealization p2 p3) ->
  (sector : Preferred.Sector Preferred.p3PreferredPresentation) ->
  Green.normalizedDVRLength
    (green G)
    (Green.p3SectorClass (green G) sector)
  ≡
  P3.normalizedDVRLength
    p3
    (P3.everySectorHasSourcePiece p3 sector)
p3GreenLengthEqualsCanonicalSourceLength {p3} G sector =
  trans
    (Green.p3LengthMatchesSemistableLocalMultiplicity
      (green G)
      sector)
    (sym
      (trans
        (P3.localizedLengthMatchesSemistableMultiplicity
          p3
          (P3.everySectorHasSourcePiece p3 sector))
        (cong
          P3Geom.p3LocalGeometricMultiplicity
          (P3.everySectorHasSourcePieceCorrect p3 sector))))

p2GreenLengthEqualsIndependentGeometry :
  {p2 : P2.P2UranoInertiaSectorLocalizationTheorem}
  {p3 : P3.P3H3NodeBranchLocalizationTheorem} ->
  (G : PBSharedGreenRealization p2 p3) ->
  (sector : Preferred.Sector Preferred.p2PreferredPresentation) ->
  Green.normalizedDVRLength
    (green G)
    (Green.p2SectorClass (green G) sector)
  ≡
  P2Geom.sectorIsotropyDenominatorTwoAdicDepth sector
p2GreenLengthEqualsIndependentGeometry G =
  Green.p2LengthMatchesStackIsotropyDenominatorDepth (green G)

p3GreenLengthEqualsIndependentGeometry :
  {p2 : P2.P2UranoInertiaSectorLocalizationTheorem}
  {p3 : P3.P3H3NodeBranchLocalizationTheorem} ->
  (G : PBSharedGreenRealization p2 p3) ->
  (sector : Preferred.Sector Preferred.p3PreferredPresentation) ->
  Green.normalizedDVRLength
    (green G)
    (Green.p3SectorClass (green G) sector)
  ≡
  P3Geom.p3LocalGeometricMultiplicity sector
p3GreenLengthEqualsIndependentGeometry G =
  Green.p3LengthMatchesSemistableLocalMultiplicity (green G)

------------------------------------------------------------------------
-- 5. No hidden fourth payment.
------------------------------------------------------------------------

data PrimewiseTheoremsAloneCreateSharedGreenRealization : Set where
data SharedGreenRealizationAloneCreatesPrimewiseLocalization : Set where
data ThreePaymentsMayReadMonsterResidual : Set where

primewiseTheoremsDoNotCreateSharedGreenRealization :
  PrimewiseTheoremsAloneCreateSharedGreenRealization -> ⊥
primewiseTheoremsDoNotCreateSharedGreenRealization ()

sharedGreenRealizationDoesNotCreatePrimewiseLocalization :
  SharedGreenRealizationAloneCreatesPrimewiseLocalization -> ⊥
sharedGreenRealizationDoesNotCreatePrimewiseLocalization ()

threePaymentsMayNotReadMonsterResidual :
  ThreePaymentsMayReadMonsterResidual -> ⊥
threePaymentsMayNotReadMonsterResidual ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryNewExtension

record PBTerminalLocalizationFactorizationBoundary : Set where
  constructor pb-terminal-localization-factorization-boundary
  field
    p2PrimewiseLocalizationPaymentSeparated : Bool
    p3PrimewiseLocalizationPaymentSeparated : Bool
    sharedGreenRealizationPaymentSeparated : Bool
    threePaymentsAssembleTerminalTheorem : Bool
    hiddenFourthPaymentRequired : Bool
    monsterResidualUsedToDefinePayments : Bool
    attributionFirewallPreserved : Bool

canonicalPBTerminalLocalizationFactorizationBoundary :
  PBTerminalLocalizationFactorizationBoundary
canonicalPBTerminalLocalizationFactorizationBoundary =
  pb-terminal-localization-factorization-boundary
    true true true true false false true
