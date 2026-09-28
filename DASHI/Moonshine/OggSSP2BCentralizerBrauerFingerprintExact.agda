module DASHI.Moonshine.OggSSP2BCentralizerBrauerFingerprintExact where

------------------------------------------------------------------------
-- 2B LOCAL-CENTRALIZER BRAUER FINGERPRINT
--
-- EXTERNAL SOURCES
--
-- ATLAS:
--   C_M(2B) has shape 2^(1+24).Co1.
--   Co1 has many 2-regular conjugacy classes and explicit characteristic-2
--   representations (including dimensions 24 and 274).
--
-- Standard modular representation theory:
--   a normal p-subgroup acts trivially on every irreducible module in
--   characteristic p.  Hence simple characteristic-2 composition factors of
--   the 2B centralizer factor through the Co1 quotient.
--
-- Carnahan, Corollary 3.25:
--   the 2B Tate cohomology carries Brauer characters evaluated on 2-regular
--   elements h in the Monster centralizer.
--
-- DASHI CONSEQUENCE
--
-- A source-native refinement finer than cyclic C2/C4 lattice type can be
-- represented by its local-centralizer Brauer fingerprint on Co1 2-regular
-- probes.
--
-- IMPORTANT
--
-- Five probes do NOT imply five source classes.
-- This module constructs the fingerprint language and a recognition socket;
-- it does not manufacture five distinct fingerprints or a sector assignment.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.OggSSP2BUranoIntegralModuleParityExact as Urano
import DASHI.Moonshine.OggSSPP2GreenClassSectorRecognitionExact as GreenRecognition
import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Sector
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Source atlas.
------------------------------------------------------------------------

atlasMonsterTwoBCentralizer : Source.AttributedSource
atlasMonsterTwoBCentralizer =
  Source.mkNoDOISource
    "ATLAS of Finite Group Representations"
    "Monster group M: 2B centralizer and maximal 2-local subgroup"
    "ATLAS web database"
    ""
    "https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M/"
    (Source.namedSourceKind "group-theory database")
    "records the Monster 2B centralizer/maximal-subgroup shape 2^(1+24).Co1; used only to identify the local-centralizer quotient, not to source a five-sector Moonshine localization"
    Source.publicAttribution

atlasCo1Modular : Source.AttributedSource
atlasCo1Modular =
  Source.mkNoDOISource
    "ATLAS of Finite Group Representations"
    "Conway group Co1: conjugacy classes and modular representations"
    "ATLAS web database"
    ""
    "https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/Co1/"
    (Source.namedSourceKind "group-theory database")
    "records Co1 conjugacy classes, including multiple odd-order 2-regular classes, and explicit characteristic-2 matrix representations; used as a source-native Brauer probe space, not as authority for DASHI inertia labels"
    Source.publicAttribution

serreModularRepresentation : Source.AttributedSource
serreModularRepresentation =
  Source.mkNoDOISource
    "Jean-Pierre Serre"
    "Linear Representations of Finite Groups"
    "Graduate Texts in Mathematics 42, Springer"
    "1977"
    "https://link.springer.com/book/10.1007/978-1-4684-9458-7"
    Source.academicBookSource
    "standard modular-representation framework: a normal p-subgroup is in the kernel of every irreducible representation in characteristic p; used to justify passage from simple 2B-centralizer composition factors to the Co1 quotient"
    Source.publicAttribution

carnahanIntegralForm : Source.AttributedSource
carnahanIntegralForm =
  Source.mkDOISource
    "Scott Carnahan"
    "A Self-Dual Integral Form of the Moonshine Module"
    "Symmetry, Integrability and Geometry: Methods and Applications 15, 030"
    "2019"
    "10.3842/SIGMA.2019.030"
    "https://doi.org/10.3842/SIGMA.2019.030"
    Source.academicArticleSource
    "Corollary 3.25 evaluates 2B Tate-cohomology Brauer characters on p-regular elements of the Monster centralizer; does not provide a five-sector characteristic-2 inertia localization"
    Source.publicAttribution

twoBCentralizerBrauerFingerprintSourceAtlas : Source.AttributedSourceAtlas
twoBCentralizerBrauerFingerprintSourceAtlas =
  Source.mkSourceAtlas
    "2B local-centralizer Brauer fingerprint"
    "DASHI.Moonshine.OggSSP2BCentralizerBrauerFingerprintExact"
    (atlasMonsterTwoBCentralizer
      ∷ atlasCo1Modular
      ∷ serreModularRepresentation
      ∷ carnahanIntegralForm
      ∷ [])
    "ATLAS owns centralizer/Co1 group data, Serre owns the modular normal-p-subgroup principle, and Carnahan owns the 2B Tate Brauer-character formula; DASHI owns only the fingerprint cutset and future sector-recognition obligation"

------------------------------------------------------------------------
-- 2. Five explicit 2-regular Co1 probes.
--
-- These are only evaluation coordinates.  No claim is made that five probes
-- yield five distinct source fingerprints.
------------------------------------------------------------------------

data Co1TwoRegularProbe : Set where
  co1Class1A :
    Co1TwoRegularProbe
  co1Class3A :
    Co1TwoRegularProbe
  co1Class3B :
    Co1TwoRegularProbe
  co1Class3C :
    Co1TwoRegularProbe
  co1Class3D :
    Co1TwoRegularProbe

data ProbeOrder : Set where
  orderOne :
    ProbeOrder
  orderThree :
    ProbeOrder

probeOrder :
  Co1TwoRegularProbe ->
  ProbeOrder
probeOrder co1Class1A = orderOne
probeOrder co1Class3A = orderThree
probeOrder co1Class3B = orderThree
probeOrder co1Class3C = orderThree
probeOrder co1Class3D = orderThree

probeIsTwoRegular :
  Co1TwoRegularProbe ->
  Bool
probeIsTwoRegular probe = true

probeIsTwoRegularIsTrue :
  (probe : Co1TwoRegularProbe) ->
  probeIsTwoRegular probe ≡ true
probeIsTwoRegularIsTrue probe = refl

------------------------------------------------------------------------
-- 3. Abstract Brauer fingerprint.
--
-- Brauer values are not forced to Nat: they may live in a cyclotomic /
-- residue-field value type chosen by the actual source theorem.
------------------------------------------------------------------------

record TwoBBrauerFingerprint : Set₁ where
  field
    BrauerValue :
      Set

    value :
      Co1TwoRegularProbe ->
      BrauerValue

open TwoBBrauerFingerprint public

record P2CentralizerBrauerSource : Set₁ where
  field
    SourcePiece :
      Set

    Fingerprint :
      Set

    degreeParity :
      SourcePiece ->
      Urano.DegreeParity

    moduleTag :
      SourcePiece ->
      Urano.TwoBModuleTag

    brauerFingerprint :
      SourcePiece ->
      Fingerprint

    sourcePieceComesFromIntegralTwoBTateObject :
      SourcePiece ->
      Bool

    sourcePieceComesFromIntegralTwoBTateObjectIsTrue :
      (piece : SourcePiece) ->
      sourcePieceComesFromIntegralTwoBTateObject piece ≡ true

    respectsUranoForbiddenPairs :
      (piece : SourcePiece) ->
      Urano.TwoBSourceForbidden
        (degreeParity piece)
        (moduleTag piece)
      ->
      ⊥

    fingerprintRetainsCo1BrauerData :
      SourcePiece ->
      Bool

    fingerprintRetainsCo1BrauerDataIsTrue :
      (piece : SourcePiece) ->
      fingerprintRetainsCo1BrauerData piece ≡ true

    fingerprintComputedFromTwoRegularCentralizerAction :
      SourcePiece ->
      Bool

    fingerprintComputedFromTwoRegularCentralizerActionIsTrue :
      (piece : SourcePiece) ->
      fingerprintComputedFromTwoRegularCentralizerAction piece ≡ true

    fingerprintDefinedWithoutMonsterResidualTen :
      Bool
    fingerprintDefinedWithoutMonsterResidualTenIsTrue :
      fingerprintDefinedWithoutMonsterResidualTen ≡ true

    fingerprintDefinedWithoutBase369Labels :
      Bool
    fingerprintDefinedWithoutBase369LabelsIsTrue :
      fingerprintDefinedWithoutBase369Labels ≡ true

open P2CentralizerBrauerSource public

------------------------------------------------------------------------
-- 4. Adapter to the generic source Green-class refinement.
------------------------------------------------------------------------

asSourceGreenClassRefinement :
  P2CentralizerBrauerSource ->
  GreenRecognition.P2SourceGreenClassRefinement
asSourceGreenClassRefinement source =
  record
    { GreenRecognition.SourcePiece =
        SourcePiece source

    ; GreenRecognition.GreenClass =
        Fingerprint source

    ; GreenRecognition.degreeParity =
        degreeParity source

    ; GreenRecognition.moduleTag =
        moduleTag source

    ; GreenRecognition.greenClass =
        brauerFingerprint source

    ; GreenRecognition.sourcePieceComesFromIntegralTwoBWeightSpace =
        sourcePieceComesFromIntegralTwoBTateObject source

    ; GreenRecognition.sourcePieceComesFromIntegralTwoBWeightSpaceIsTrue =
        sourcePieceComesFromIntegralTwoBTateObjectIsTrue source

    ; GreenRecognition.respectsUranoForbiddenPairs =
        respectsUranoForbiddenPairs source

    ; GreenRecognition.greenClassComesFromRelevantIntegralGreenRing =
        fingerprintRetainsCo1BrauerData source

    ; GreenRecognition.greenClassComesFromRelevantIntegralGreenRingIsTrue =
        fingerprintRetainsCo1BrauerDataIsTrue source

    ; GreenRecognition.greenClassRetainsMonsterLocalCentralizerAction =
        fingerprintComputedFromTwoRegularCentralizerAction source

    ; GreenRecognition.greenClassRetainsMonsterLocalCentralizerActionIsTrue =
        fingerprintComputedFromTwoRegularCentralizerActionIsTrue source

    ; GreenRecognition.greenClassSupportsGeneralizedBrauerCharacter =
        fingerprintComputedFromTwoRegularCentralizerAction source

    ; GreenRecognition.greenClassSupportsGeneralizedBrauerCharacterIsTrue =
        fingerprintComputedFromTwoRegularCentralizerActionIsTrue source

    ; GreenRecognition.refinementDefinedWithoutMonsterResidualTen =
        fingerprintDefinedWithoutMonsterResidualTen source

    ; GreenRecognition.refinementDefinedWithoutMonsterResidualTenIsTrue =
        fingerprintDefinedWithoutMonsterResidualTenIsTrue source

    ; GreenRecognition.refinementDefinedWithoutBase369Labels =
        fingerprintDefinedWithoutBase369Labels source

    ; GreenRecognition.refinementDefinedWithoutBase369LabelsIsTrue =
        fingerprintDefinedWithoutBase369LabelsIsTrue source
    }

------------------------------------------------------------------------
-- 5. The remaining recognition theorem.
------------------------------------------------------------------------

record P2CentralizerBrauerSectorRecognition
    (source : P2CentralizerBrauerSource) : Set₁ where
  field
    sectorOfFingerprint :
      Fingerprint source ->
      Sector.BinaryTetrahedralInversionOrbit

    localizedSector :
      SourcePiece source ->
      Sector.BinaryTetrahedralInversionOrbit

    localizedSectorFactorsThroughBrauerFingerprint :
      (piece : SourcePiece source) ->
      localizedSector piece
      ≡
      sectorOfFingerprint (brauerFingerprint source piece)

    everySectorHasSourcePiece :
      (sector : Sector.BinaryTetrahedralInversionOrbit) ->
      SourcePiece source

    everySectorHasSourcePieceCorrect :
      (sector : Sector.BinaryTetrahedralInversionOrbit) ->
      localizedSector (everySectorHasSourcePiece sector) ≡ sector

    recognitionComesFromSourceBrauerData :
      Bool
    recognitionComesFromSourceBrauerDataIsTrue :
      recognitionComesFromSourceBrauerData ≡ true

    recognitionIndependentOfMonsterResidualTen :
      Bool
    recognitionIndependentOfMonsterResidualTenIsTrue :
      recognitionIndependentOfMonsterResidualTen ≡ true

    recognitionIndependentOfBase369Labels :
      Bool
    recognitionIndependentOfBase369LabelsIsTrue :
      recognitionIndependentOfBase369Labels ≡ true

open P2CentralizerBrauerSectorRecognition public

asGreenClassSectorRecognition :
  (source : P2CentralizerBrauerSource) ->
  P2CentralizerBrauerSectorRecognition source ->
  GreenRecognition.P2GreenClassSectorRecognition
    (asSourceGreenClassRefinement source)
asGreenClassSectorRecognition source recognition =
  record
    { GreenRecognition.sectorOfGreenClass =
        sectorOfFingerprint recognition

    ; GreenRecognition.localizedSector =
        localizedSector recognition

    ; GreenRecognition.localizedSectorFactorsThroughGreenClass =
        localizedSectorFactorsThroughBrauerFingerprint recognition

    ; GreenRecognition.everySectorHasSourcePiece =
        everySectorHasSourcePiece recognition

    ; GreenRecognition.everySectorHasSourcePieceCorrect =
        everySectorHasSourcePieceCorrect recognition

    ; GreenRecognition.recognitionIndependentOfMonsterResidualTen =
        recognitionIndependentOfMonsterResidualTen recognition

    ; GreenRecognition.recognitionIndependentOfMonsterResidualTenIsTrue =
        recognitionIndependentOfMonsterResidualTenIsTrue recognition

    ; GreenRecognition.recognitionIndependentOfBase369Labels =
        recognitionIndependentOfBase369Labels recognition

    ; GreenRecognition.recognitionIndependentOfBase369LabelsIsTrue =
        recognitionIndependentOfBase369LabelsIsTrue recognition
    }

------------------------------------------------------------------------
-- 6. Capacity is not recognition.
------------------------------------------------------------------------

data FiveProbesCreateFiveFingerprints : Set where
data ExplicitCo1RepresentationsCreateSectorMap : Set where
data CentralizerShapeCreatesBrauerDecomposition : Set where
data BrauerFingerprintAutomaticallyPaysDVRLengths : Set where

fiveProbesDoNotCreateFiveFingerprints :
  FiveProbesCreateFiveFingerprints -> ⊥
fiveProbesDoNotCreateFiveFingerprints ()

explicitCo1RepresentationsDoNotCreateSectorMap :
  ExplicitCo1RepresentationsCreateSectorMap -> ⊥
explicitCo1RepresentationsDoNotCreateSectorMap ()

centralizerShapeDoesNotCreateBrauerDecomposition :
  CentralizerShapeCreatesBrauerDecomposition -> ⊥
centralizerShapeDoesNotCreateBrauerDecomposition ()

brauerFingerprintDoesNotAutomaticallyPayDVRLengths :
  BrauerFingerprintAutomaticallyPaysDVRLengths -> ⊥
brauerFingerprintDoesNotAutomaticallyPayDVRLengths ()

data P2CentralizerBrauerSourceInhabited : Set where
data P2CentralizerBrauerSectorRecognitionInhabited : Set where

centralizerBrauerSourceStillOpen :
  P2CentralizerBrauerSourceInhabited -> ⊥
centralizerBrauerSourceStillOpen ()

centralizerBrauerSectorRecognitionStillOpen :
  P2CentralizerBrauerSectorRecognitionInhabited -> ⊥
centralizerBrauerSectorRecognitionStillOpen ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record P2CentralizerBrauerFingerprintBoundary : Set where
  constructor p2-centralizer-brauer-fingerprint-boundary
  field
    monsterTwoBCentralizerShapeSourced : Bool
    normalTwoSubgroupQuotientPrincipleSourced : Bool
    co1TwoRegularProbeClassesSourced : Bool
    characteristicTwoCo1RepresentationDataExists : Bool
    carnahanTwoBBrauerCentralizerFormulaSourced : Bool
    sourceNativeFingerprintLanguageDefined : Bool
    adapterToGreenClassRefinementOwned : Bool
    fiveProbesAssertedToGiveFiveClasses : Bool
    centralizerBrauerSourceInhabited : Bool
    centralizerBrauerSectorRecognitionInhabited : Bool
    sectorLengthsPaidByFingerprintAlone : Bool
    monsterResidualUsedToDefineFingerprint : Bool
    base369UsedToDefineFingerprint : Bool
    attributionFirewallPreserved : Bool

canonicalP2CentralizerBrauerFingerprintBoundary :
  P2CentralizerBrauerFingerprintBoundary
canonicalP2CentralizerBrauerFingerprintBoundary =
  p2-centralizer-brauer-fingerprint-boundary
    true true true true true true true
    false false false false false false true
