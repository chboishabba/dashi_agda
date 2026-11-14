module DASHI.Moonshine.Monster3BAtlasSymplectic12SourceReceiptExact where

------------------------------------------------------------------------
-- ATLAS / CTblLib SOURCE RECEIPT FOR THE 3B NORMALIZER 12-MODULE
--
-- Two independent ATLAS/verification surfaces identify the exact source data
-- needed by the repository's finite Heisenberg carrier.
--
-- (1) Direct quotient module.
--     The ATLAS Suzuki data publish absolutely irreducible 12-dimensional
--     GF(3) representations for 2.Suz and 2.Suz:2.  The exact MeatAxe bytes are
--     now vendored in `data/atlas/`, with SHA-256/provenance pinned by
--     `monster3b_suz12_source_manifest_20261012.json`.
--
-- (2) Monster-3B semidirect-product realization.
--     Breuer--Magaard--Wilson, Appendix 9.2, uses the ATLAS faithful 38-
--     dimensional GF(3) representation of
--
--         H = 3^(1+12) : 6.Suz.2
--
--     with files `M3max7G0-f3r38B0.m1` ... `.m4`.  Those matrices are block
--     diagonal of sizes 24 and 14; the lower-right blocks generate
--
--         H/X ~= 3_+^(1+12) : 2.Suz.2.
--
-- COMPUTED DIRECT-MODULE NUANCE:
-- The inner 2.Suz pair fixes a unique alternating form.  On that same form the
-- first generator of the direct 2.Suz:2 representation has similitude
-- multiplier 2 = -1 in F3, while its second generator is literally the old
-- inner second generator and has multiplier 1.  Thus the concrete extension is
-- treated as a center-sensitive symplectic-similitude action, not silently
-- promoted to strict Sp(12,3) matrix equality.  This is compatible with the
-- extraspecial-group role where the outer action may invert the center.
--
-- AUTHORITY BOUNDARY:
-- bytes/provenance are now paid.  Agda-kernel proof of the same-basis
-- X6 + X6* intertwiner and the full Heisenberg central correction remain
-- separate obligations; the exact finite numerical receipt is owned elsewhere.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record AtlasMatrixFile : Set where
  constructor atlas-matrix-file
  field
    fileName : String
    fieldOrder : Nat
    ambientDimension : Nat
open AtlasMatrixFile public

matrix1 matrix2 matrix3 matrix4 : AtlasMatrixFile
matrix1 = atlas-matrix-file "M3max7G0-f3r38B0.m1" 3 38
matrix2 = atlas-matrix-file "M3max7G0-f3r38B0.m2" 3 38
matrix3 = atlas-matrix-file "M3max7G0-f3r38B0.m3" 3 38
matrix4 = atlas-matrix-file "M3max7G0-f3r38B0.m4" 3 38

record AtlasDirectTwelveModuleReceipt : Set where
  constructor atlas-direct-twelve-module-receipt
  field
    atlasGroup : String
    atlasRepresentationId : String
    fieldOrder : Nat
    dimension : Nat
    absolutelyIrreducible : Bool
    standardGenerators : Bool
    downloadableGapMatrices : Bool
open AtlasDirectTwelveModuleReceipt public

canonicalDirectTwelveModuleReceipt : AtlasDirectTwelveModuleReceipt
canonicalDirectTwelveModuleReceipt =
  atlas-direct-twelve-module-receipt
    "2.Suz:2"
    "2Suzd2G1-f3r12aB0"
    3
    12
    true
    true
    true

matrixManifestPath : String
matrixManifestPath = "data/atlas/monster3b_suz12_source_manifest_20261012.json"

compressionReceiptPath : String
compressionReceiptPath = "outputs/monster3b_atlas_compression_field_selector_20261012.json"

record Atlas3BNormalizerSourceReceipt : Set where
  constructor atlas-3b-normalizer-source-receipt
  field
    sourceTitle : String
    sourceSection : String
    atlasGroupName : String
    sourceFieldOrder : Nat
    faithfulAmbientDimension : Nat
    firstBlockDimension : Nat
    secondBlockDimension : Nat
    extraspecialQuotientDimension : Nat
    sourceStatesTwelveDimensionalIrreducible : Bool
    sourceStatesSymplecticFormPreserved : Bool
    sourceStatesEmbeddingInSp12_3 : Bool
    sourceStatesExtraspecialAutomorphismInterpretation : Bool
    lowerRightFourteenGeneratesExtension : Bool
    fourthGeneratorRedundantForHmodX : Bool
    directTwelveModuleAvailable : Bool
    matrixEntriesImportedHere : Bool
    directOuterGeneratorSimilitudeMultiplierTwoComputed : Bool
    directSecondGeneratorEqualsInnerSecondComputed : Bool
    repositorySymplecticBasisIntertwinerKernelPaid : Bool
open Atlas3BNormalizerSourceReceipt public

canonicalAtlas3BNormalizerSourceReceipt : Atlas3BNormalizerSourceReceipt
canonicalAtlas3BNormalizerSourceReceipt =
  atlas-3b-normalizer-source-receipt
    "Breuer-Magaard-Wilson: Some steps in the verification of the ordinary character table of the Monster group"
    "Appendix 9.2: A permutation representation of H/X"
    "3^(1+12):6.Suz.2"
    3
    38
    24
    14
    12
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    false

matrixAcquisitionBase : String
matrixAcquisitionBase =
  "ATLAS of Group Representations; public mirror wilcompute/W33-Theory@509d5b136f3d4efd0cf9be016700fd7886fc9e34"

record Boundary : Set where
  constructor boundary
  field
    certifiedAtlasNormalizerRepresentationLocated : Bool
    certifiedDirectTwelveModuleLocated : Bool
    exactNormalizerGeneratorFileNamesKnown : Bool
    sourceSymplectic12ActionExists : Bool
    sourceEmbedsNormalizerQuotientInSp12_3 : Bool
    sourceExplainsActionOnExtraspecialQuotient : Bool
    rawMatrixEntriesInRepo : Bool
    outerSimilitudeMultiplierComputed : Bool
    sameBasisX6PlusDualIntertwinerRuntimePaid : Bool
    sameBasisX6PlusDualIntertwinerKernelPaid : Bool
    sourceNativeHeisenbergConjugationPaid : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary true true true true true true true true true false false
