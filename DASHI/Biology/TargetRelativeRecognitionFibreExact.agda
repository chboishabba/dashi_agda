module DASHI.Biology.TargetRelativeRecognitionFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.BioactiveMolecularRecognitionBridge as Recognition
import DASHI.Biology.IonicMimicryGeometryExact as Ionic
import DASHI.Biology.Kluver5HT2AMolecularProteinInstantiationExact as FiveHT2A
import DASHI.Biology.FiveHT2ASignalingDialecticExact as Signaling

------------------------------------------------------------------------
-- TARGET-RELATIVE RECOGNITION FIBRE
--
-- A biological target does not compare whole molecular identities by an
-- all-or-nothing equality test.  Recognition can depend on selected local
-- coordinates.  The same pair may therefore be:
--
--   similar enough for target A,
--   distinguishable for target B,
--   and functionally divergent downstream.
--
-- Ionic mimicry (Pb2+/Ca2+) and ligand/receptor recognition
-- (serotonin/LSD/5-HT2A) are represented as two instances of this abstract
-- partial-coordinate principle, not as the same chemistry.
------------------------------------------------------------------------

data RecognitionCoordinate : Set where
  scaffoldCoordinate : RecognitionCoordinate
  pharmacophoreCoordinate : RecognitionCoordinate
  formalChargeCoordinate : RecognitionCoordinate
  electrostaticFieldCoordinate : RecognitionCoordinate
  sizeShapeCoordinate : RecognitionCoordinate
  localGeometryCoordinate : RecognitionCoordinate
  coordinationGeometryCoordinate : RecognitionCoordinate
  donorAcceptorCoordinate : RecognitionCoordinate
  hydrationSolvationCoordinate : RecognitionCoordinate
  stereochemistryCoordinate : RecognitionCoordinate
  conformationCoordinate : RecognitionCoordinate
  targetFlexibilityCoordinate : RecognitionCoordinate
  kineticCoordinate : RecognitionCoordinate

data CoordinateRelation : Set where
  sufficientlyOverlappingForTarget : CoordinateRelation
  experimentallyDistinguishable : CoordinateRelation
  sourceConditionedOverlap : CoordinateRelation
  unresolvedCoordinate : CoordinateRelation

record RecognitionCoordinateComparison : Set where
  constructor recognitionCoordinateComparison
  field
    leftIdentity : String
    rightIdentity : String
    target : String
    coordinate : RecognitionCoordinate
    relation : CoordinateRelation
    evidenceReference : String

open RecognitionCoordinateComparison public

------------------------------------------------------------------------
-- Ionic instance.
------------------------------------------------------------------------

pbCaChargeComparison : RecognitionCoordinateComparison
pbCaChargeComparison =
  recognitionCoordinateComparison
    "Ca2+"
    "Pb2+"
    "calcium-binding protein site"
    formalChargeCoordinate
    sufficientlyOverlappingForTarget
    "DASHI.Biology.IonicMimicryGeometryExact.pbCaChargeOverlap"

pbCaCoordinationComparison : RecognitionCoordinateComparison
pbCaCoordinationComparison =
  recognitionCoordinateComparison
    "Ca2+"
    "Pb2+"
    "calcium-binding protein site"
    coordinationGeometryCoordinate
    experimentallyDistinguishable
    "DASHI.Biology.IonicMimicryGeometryExact.pbCaCoordinationDifference"

------------------------------------------------------------------------
-- 5-HT2A ligand instance.
--
-- We deliberately do not assert a naive serotonin ~= LSD whole-molecule
-- similarity.  The structural sources show that both can occupy 5-HT2A
-- receptor binding-state families while ligand-dependent receptor-state
-- differences remain measurable.
------------------------------------------------------------------------

serotoninLSDTargetComparison : RecognitionCoordinateComparison
serotoninLSDTargetComparison =
  recognitionCoordinateComparison
    "serotonin / 5-HT"
    "LSD"
    "human 5-HT2A receptor"
    pharmacophoreCoordinate
    sourceConditionedOverlap
    "Kim et al. 2020 / Gumpper et al. 2025 structural receptor evidence"

serotoninLSDConformationComparison : RecognitionCoordinateComparison
serotoninLSDConformationComparison =
  recognitionCoordinateComparison
    "serotonin / 5-HT"
    "LSD"
    "human 5-HT2A receptor"
    conformationCoordinate
    experimentallyDistinguishable
    "comparative ligand-dependent active-state 5-HT2A structural evidence"

canonicalRecognitionCoordinateComparisons :
  List RecognitionCoordinateComparison
canonicalRecognitionCoordinateComparisons =
  pbCaChargeComparison
  ∷ pbCaCoordinationComparison
  ∷ serotoninLSDTargetComparison
  ∷ serotoninLSDConformationComparison
  ∷ []

------------------------------------------------------------------------
-- Existing repo recognition vocabulary embeds into the generalized fibre.
------------------------------------------------------------------------

recognitionSimilarityCarriers :
  List Recognition.BioactiveSimilarityCarrier
recognitionSimilarityCarriers =
  Recognition.canonicalBioactiveSimilarityCarriers

ionicMimicryBoundary :
  Ionic.IonicMimicryGeometryBoundary
ionicMimicryBoundary =
  Ionic.canonicalIonicMimicryGeometryBoundary

fiveHT2ASignalingBoundary :
  Signaling.FiveHT2ASignalingDialectic
fiveHT2ASignalingBoundary =
  Signaling.canonicalFiveHT2ASignalingDialectic

------------------------------------------------------------------------
-- Target-relative semantics.
------------------------------------------------------------------------

record TargetRelativeRecognitionFibre : Set where
  constructor targetRelativeRecognitionFibre
  field
    leftIdentity : String
    rightIdentity : String
    targetIdentity : String
    overlappingCoordinates : List RecognitionCoordinate
    separatingCoordinates : List RecognitionCoordinate
    protocolReference : String

    overlapCanPermitRecognition : Bool
    overlapCanPermitRecognitionIsTrue :
      overlapCanPermitRecognition ≡ true

    overlapImpliesWholeIdentity : Bool
    overlapImpliesWholeIdentityIsFalse :
      overlapImpliesWholeIdentity ≡ false

    overlapImpliesSameDownstreamAction : Bool
    overlapImpliesSameDownstreamActionIsFalse :
      overlapImpliesSameDownstreamAction ≡ false

    recognitionIsTargetIndependent : Bool
    recognitionIsTargetIndependentIsFalse :
      recognitionIsTargetIndependent ≡ false

open TargetRelativeRecognitionFibre public

canonicalPbCaRecognitionFibre : TargetRelativeRecognitionFibre
canonicalPbCaRecognitionFibre =
  targetRelativeRecognitionFibre
    "Ca2+"
    "Pb2+"
    "Ca2+-binding site"
    ( formalChargeCoordinate
    ∷ donorAcceptorCoordinate
    ∷ sizeShapeCoordinate
    ∷ []
    )
    ( coordinationGeometryCoordinate
    ∷ hydrationSolvationCoordinate
    ∷ targetFlexibilityCoordinate
    ∷ []
    )
    "site/source specific"
    true refl
    false refl
    false refl
    false refl

canonicalSerotoninLSDRecognitionFibre : TargetRelativeRecognitionFibre
canonicalSerotoninLSDRecognitionFibre =
  targetRelativeRecognitionFibre
    "serotonin / 5-HT"
    "LSD"
    "human 5-HT2A receptor"
    ( pharmacophoreCoordinate
    ∷ electrostaticFieldCoordinate
    ∷ localGeometryCoordinate
    ∷ []
    )
    ( scaffoldCoordinate
    ∷ conformationCoordinate
    ∷ kineticCoordinate
    ∷ []
    )
    "source/assay structural and signaling context"
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Anti-collapse.
------------------------------------------------------------------------

data SameTargetMeansMoleculesLookTheSame : Set where
data PartialGeometryMatchMeansSameMolecule : Set where
data ReceptorRecognitionMeansSameSignaling : Set where
data IonicMimicryAndLigandMimicryAreSameMechanism : Set where

sameTargetDoesNotMeanSameMolecule :
  SameTargetMeansMoleculesLookTheSame → ⊥
sameTargetDoesNotMeanSameMolecule ()

partialGeometryMatchDoesNotMeanSameMolecule :
  PartialGeometryMatchMeansSameMolecule → ⊥
partialGeometryMatchDoesNotMeanSameMolecule ()

recognitionDoesNotMeanSameSignaling :
  ReceptorRecognitionMeansSameSignaling → ⊥
recognitionDoesNotMeanSameSignaling ()

ionicAndLigandMimicryRemainDistinct :
  IonicMimicryAndLigandMimicryAreSameMechanism → ⊥
ionicAndLigandMimicryRemainDistinct ()

------------------------------------------------------------------------
-- General interpretation.
------------------------------------------------------------------------

recognitionFibreReading : String
recognitionFibreReading =
  "Biological molecular recognition is best represented here as a target-relative partial-coordinate match: charge, local geometry, pharmacophore, donor/acceptor layout, solvation, conformational accommodation and kinetics can overlap or separate independently. Pb2+/Ca2+ and serotonin/LSD are distinct examples of the general architecture, not instances of one identical mechanism."
