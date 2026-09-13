module DASHI.Physics.Chemistry.AtomicPeriodicTable369ProteinDNA3DAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.DNAChemistryCarrier as DNA
import DASHI.Biology.Physical.DNAHelixDihedralExact as Helix
import DASHI.Biology.Physical.BDNACalibratedHelicalGeometryExact as B
import DASHI.Biology.Physical.BDNAStepSE3CompositionExact as SE3DNA
import DASHI.Geometry.RigidMotionSemidirectProductExact as SE3
import DASHI.Biology.Protein.ProteinConformationAttractor as Protein
import DASHI.Biology.Molecular.MolecularAssemblyBoundary as Molecule

------------------------------------------------------------------------
-- PROTEIN / DNA 3-D ADAPTER
--
-- This owner does not identify sequence with geometry.  It records the exact
-- maps already present in the repo and exposes them as donors for the atomic ->
-- molecular symmetry/reconstruction lane.
------------------------------------------------------------------------

-- DNA: exact finite chemistry coordinate change.
dnaToUV : DNA.DNABase → DNA.UVCoordinate
dnaToUV = DNA.toUV

dnaFromUV : DNA.UVCoordinate → DNA.DNABase
dnaFromUV = DNA.fromUV

dnaFromUVToUVExact : (b : DNA.DNABase) → dnaFromUV (dnaToUV b) ≡ b
dnaFromUVToUVExact = DNA.fromUV-toUV

dnaToUVFromUVExact : (q : DNA.UVCoordinate) → dnaToUV (dnaFromUV q) ≡ q
dnaToUVFromUVExact = DNA.toUV-fromUV

dnaComplementEquivariant :
  (b : DNA.DNABase) →
  DNA.toUV (DNA.complement b) ≡ DNA.complementUV (DNA.toUV b)
dnaComplementEquivariant = DNA.complement-UV-equivariant

-- DNA: exact finite helical reflection/rotation law.
dnaDihedralConjugation :
  (p : Helix.Phase4) →
  Helix.reflect (Helix.rotate (Helix.reflect p)) ≡ Helix.rotateInv p
dnaDihedralConjugation = Helix.dihedralConjugation

-- Physical DNA geometry is carried by sequence/environment-dependent rigid
-- steps and ordered rigid-motion composition, not by the base alphabet itself.
dnaRigidStepCalibrationSurface :
  (model : SE3.RigidMotionModel) → Set₁
dnaRigidStepCalibrationSurface model = SE3DNA.BDNARigidStepCalibration model

-- Protein: sequence indexes a conformational system with environment, basin,
-- admissibility, and potentially multiple attractors.
proteinConformationSurface : Set₁
proteinConformationSurface = Protein.ProteinConformationSystem

proteinMultipleAttractorSurface :
  Protein.ProteinConformationSystem → Set₁
proteinMultipleAttractorSurface = Protein.MultipleAttractorWitness

molecularStereoSurface : Set₁
molecularStereoSurface = Molecule.MolecularAssemblySystem

------------------------------------------------------------------------
-- Snowball attribution coordinates.  Identifiers not verified here remain
-- explicitly unresolved rather than inferred from nearby catalogue entries.
------------------------------------------------------------------------

record ThreeDSourceCoordinate : Set where
  constructor threeDSourceCoordinate
  field
    sourceLabel : String
    doi : String
    qid : String
    dewey : String
    primaryStatus : String
    directLink : String
    sourceRole : String

watsonCrick1953 : ThreeDSourceCoordinate
watsonCrick1953 =
  threeDSourceCoordinate
    "Watson and Crick, Molecular Structure of Nucleic Acids"
    "10.1038/171737a0"
    "source-object QID unresolved in inspected repo source"
    "exact source-item Dewey unresolved"
    "primary historical paper"
    "https://doi.org/10.1038/171737a0"
    "historical structural source for the DNA double-helix model; not a calibration receipt for all B-DNA"

olson2001 : ThreeDSourceCoordinate
olson2001 =
  threeDSourceCoordinate
    "Olson et al., standard reference frame for nucleic acid base-pair geometry"
    "10.1006/jmbi.2001.4987"
    "source-object QID unresolved in inspected repo source"
    "exact source-item Dewey unresolved"
    "primary/reference-method paper"
    "https://doi.org/10.1006/jmbi.2001.4987"
    "authority for six base-pair-step coordinate conventions used by the calibrated DNA geometry owner"

record ProteinDNA3DAdapterBoundary : Set where
  constructor proteinDNA3DAdapterBoundary
  field
    dnaUsesExactCoordinateBijection : Bool
    dnaUsesExactCoordinateBijectionIsTrue :
      dnaUsesExactCoordinateBijection ≡ true

    dnaPhysicalGeometryUsesRigidMotionComposition : Bool
    dnaPhysicalGeometryUsesRigidMotionCompositionIsTrue :
      dnaPhysicalGeometryUsesRigidMotionComposition ≡ true

    proteinSequenceDefinitionallyDeterminesUniqueConformation : Bool
    proteinSequenceDefinitionallyDeterminesUniqueConformationIsFalse :
      proteinSequenceDefinitionallyDeterminesUniqueConformation ≡ false

    exactCoordinateBijectionEqualsCompleteQuantumChemistry : Bool
    exactCoordinateBijectionEqualsCompleteQuantumChemistryIsFalse :
      exactCoordinateBijectionEqualsCompleteQuantumChemistry ≡ false

    sharedSymmetryArchitectureMakesDNAAndProteinSameObject : Bool
    sharedSymmetryArchitectureMakesDNAAndProteinSameObjectIsFalse :
      sharedSymmetryArchitectureMakesDNAAndProteinSameObject ≡ false

canonicalProteinDNA3DAdapterBoundary : ProteinDNA3DAdapterBoundary
canonicalProteinDNA3DAdapterBoundary =
  proteinDNA3DAdapterBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
