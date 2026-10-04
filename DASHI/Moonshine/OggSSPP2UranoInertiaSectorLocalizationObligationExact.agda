module DASHI.Moonshine.OggSSPP2UranoInertiaSectorLocalizationObligationExact where

------------------------------------------------------------------------
-- p=2 URANO SOURCE PIECES -> INERTIA-SECTOR LOCALIZATION OBLIGATION
--
-- EXISTING SOURCE-BACKED INPUT
--
-- Urano supplies:
--   * parity-dependent exclusions for integral 2B module types;
--   * a graded Green-functional/Hauptmodul receipt;
--   * finite-length DVR generalized Brauer-character machinery upstream.
--
-- EXISTING GEOMETRIC INPUT
--
-- The characteristic-2 supersingular inertia analysis supplies five
-- loop-reversal sectors with independent 2-adic isotropy-depth weights:
--
--   identity       -> 3
--   central -1     -> 3
--   order 4        -> 2
--   order 3 pair   -> 1
--   order 6 pair   -> 1
--
-- MISSING THEOREM
--
-- Refine actual integral 2B source pieces into those five sectors, respecting
-- Urano parity exclusions, and prove normalized finite-DVR composition length
-- equals the geometric isotropy depth sectorwise.
--
-- This theorem may not be defined from the Monster residual 10 or Base369.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSP2BUranoIntegralModuleParityExact as Urano
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Sector
import DASHI.Moonshine.OggSSPP2InertiaStackDenominatorValuationExact as Geom
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Minimal theorem interface.
------------------------------------------------------------------------

record P2UranoInertiaSectorLocalizationTheorem : Set₁ where
  field
    SourcePiece :
      Set

    degreeParity :
      SourcePiece ->
      Urano.DegreeParity

    moduleTag :
      SourcePiece ->
      Urano.TwoBModuleTag

    sourcePieceComesFromIntegralTwoBWeightSpace :
      SourcePiece ->
      Bool

    sourcePieceComesFromIntegralTwoBWeightSpaceIsTrue :
      (piece : SourcePiece) ->
      sourcePieceComesFromIntegralTwoBWeightSpace piece ≡ true

    respectsUranoForbiddenPairs :
      (piece : SourcePiece) ->
      Urano.TwoBSourceForbidden
        (degreeParity piece)
        (moduleTag piece)
      ->
      ⊥

    localizedSector :
      SourcePiece ->
      Sector.BinaryTetrahedralInversionOrbit

    everySectorHasSourcePiece :
      (sector : Sector.BinaryTetrahedralInversionOrbit) ->
      SourcePiece

    everySectorHasSourcePieceCorrect :
      (sector : Sector.BinaryTetrahedralInversionOrbit) ->
      localizedSector (everySectorHasSourcePiece sector) ≡ sector

    normalizedDVRLength :
      SourcePiece ->
      Nat

    localizedLengthMatchesIsotropyDepth :
      (piece : SourcePiece) ->
      normalizedDVRLength piece
      ≡
      Geom.sectorIsotropyDenominatorTwoAdicDepth
        (localizedSector piece)

    localizationDefinedWithoutMonsterResidual :
      Bool
    localizationDefinedWithoutMonsterResidualIsTrue :
      localizationDefinedWithoutMonsterResidual ≡ true

    localizationDefinedWithoutBase369Labels :
      Bool
    localizationDefinedWithoutBase369LabelsIsTrue :
      localizationDefinedWithoutBase369Labels ≡ true

open P2UranoInertiaSectorLocalizationTheorem public

------------------------------------------------------------------------
-- 2. Representative source lengths are forced to 3,3,2,1,1.
------------------------------------------------------------------------

sectorRepresentativeLength :
  (T : P2UranoInertiaSectorLocalizationTheorem) ->
  (sector : Sector.BinaryTetrahedralInversionOrbit) ->
  normalizedDVRLength T (everySectorHasSourcePiece T sector)
  ≡
  Geom.sectorIsotropyDenominatorTwoAdicDepth sector
sectorRepresentativeLength T sector =
  trans
    (localizedLengthMatchesIsotropyDepth T
      (everySectorHasSourcePiece T sector))
    (cong Geom.sectorIsotropyDenominatorTwoAdicDepth
      (everySectorHasSourcePieceCorrect T sector))

identityLengthIsThree :
  (T : P2UranoInertiaSectorLocalizationTheorem) ->
  normalizedDVRLength T
    (everySectorHasSourcePiece T Sector.identityInertiaOrbit)
  ≡ 3
identityLengthIsThree T =
  sectorRepresentativeLength T Sector.identityInertiaOrbit

minusOneLengthIsThree :
  (T : P2UranoInertiaSectorLocalizationTheorem) ->
  normalizedDVRLength T
    (everySectorHasSourcePiece T Sector.centralMinusOneInertiaOrbit)
  ≡ 3
minusOneLengthIsThree T =
  sectorRepresentativeLength T Sector.centralMinusOneInertiaOrbit

orderFourLengthIsTwo :
  (T : P2UranoInertiaSectorLocalizationTheorem) ->
  normalizedDVRLength T
    (everySectorHasSourcePiece T Sector.orderFourInertiaOrbit)
  ≡ 2
orderFourLengthIsTwo T =
  sectorRepresentativeLength T Sector.orderFourInertiaOrbit

orderThreeLengthIsOne :
  (T : P2UranoInertiaSectorLocalizationTheorem) ->
  normalizedDVRLength T
    (everySectorHasSourcePiece T Sector.orderThreePairInertiaOrbit)
  ≡ 1
orderThreeLengthIsOne T =
  sectorRepresentativeLength T Sector.orderThreePairInertiaOrbit

orderSixLengthIsOne :
  (T : P2UranoInertiaSectorLocalizationTheorem) ->
  normalizedDVRLength T
    (everySectorHasSourcePiece T Sector.orderSixPairInertiaOrbit)
  ≡ 1
orderSixLengthIsOne T =
  sectorRepresentativeLength T Sector.orderSixPairInertiaOrbit

------------------------------------------------------------------------
-- 3. Exact source receipt and unsupported-promotion firewalls.
------------------------------------------------------------------------

uranoBoundary :
  Urano.TwoBUranoIntegralModuleParityBoundary
uranoBoundary =
  Urano.canonicalTwoBUranoIntegralModuleParityBoundary

data UranoReceiptAlreadyClassifiesFiveInertiaSectors : Set where
data UranoReceiptAlreadyProvesThreeThreeTwoOneOne : Set where
data TenTotalDefinesLocalization : Set where
data Base369NineOrbitDefinesLocalization : Set where

uranoReceiptDoesNotClassifyFiveInertiaSectors :
  UranoReceiptAlreadyClassifiesFiveInertiaSectors -> ⊥
uranoReceiptDoesNotClassifyFiveInertiaSectors ()

uranoReceiptDoesNotProveThreeThreeTwoOneOne :
  UranoReceiptAlreadyProvesThreeThreeTwoOneOne -> ⊥
uranoReceiptDoesNotProveThreeThreeTwoOneOne ()

tenTotalDoesNotDefineLocalization :
  TenTotalDefinesLocalization -> ⊥
tenTotalDoesNotDefineLocalization ()

base369NineOrbitDoesNotDefineLocalization :
  Base369NineOrbitDefinesLocalization -> ⊥
base369NineOrbitDoesNotDefineLocalization ()

------------------------------------------------------------------------
-- 4. Live wall.
------------------------------------------------------------------------

data P2UranoInertiaSectorLocalizationTheoremInhabited : Set where

p2UranoInertiaSectorLocalizationStillOpen :
  P2UranoInertiaSectorLocalizationTheoremInhabited -> ⊥
p2UranoInertiaSectorLocalizationStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.openRecognitionConjecture

record P2UranoInertiaSectorLocalizationBoundary : Set where
  constructor p2-urano-inertia-sector-localization-boundary
  field
    uranoParityExclusionsSourced : Bool
    actualIntegralTwoBPieceProvenanceRequired : Bool
    uranoGreenFunctionalSourced : Bool
    fiveInertiaSectorGeometryOwned : Bool
    isotropyDepthThreeThreeTwoOneOneOwned : Bool

    sourcePieceToFiveSectorFunctorRequired : Bool
    sourcePieceToFiveSectorFunctorInhabited : Bool
    sectorLengthsAsSourceCompositionLengthsRequired : Bool
    sectorLengthsAsSourceCompositionLengthsInhabited : Bool

    monsterResidualUsedToDefineLocalization : Bool
    base369UsedToDefineLocalization : Bool
    attributionFirewallPreserved : Bool

canonicalP2UranoInertiaSectorLocalizationBoundary :
  P2UranoInertiaSectorLocalizationBoundary
canonicalP2UranoInertiaSectorLocalizationBoundary =
  p2-urano-inertia-sector-localization-boundary
    true true true true true
    true false true false
    false false true
