module DASHI.Moonshine.Monster3BAtlasSymplectic12SourceReceiptExact where

------------------------------------------------------------------------
-- ATLAS / CTblLib SOURCE RECEIPT FOR THE 3B NORMALIZER SYMPLECTIC 12-MODULE
--
-- Two independent ATLAS/verification surfaces identify the exact source data
-- needed by the repository's finite Heisenberg carrier.
--
-- (1) Direct quotient module.
--     The ATLAS Suzuki page publishes an absolutely irreducible 12-dimensional
--     GF(3) matrix representation of `2.Suz:2` (and the corresponding 12-
--     dimensional representation of `2.Suz`).  Thus we do not need to recover
--     the linear quotient module indirectly from a larger Monster matrix.
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
--     The source explicitly states that the 12-dimensional irreducible
--     `2.Suz.2` module over GF(3) preserves a symplectic form and embeds
--     `2.Suz.2` in `Sp(12,3)`, the automorphism group of the extraspecial
--     `3_+^(1+12)`.  This is exactly the source-side quotient action required
--     to normalize the repository Heisenberg group.
--
-- IMPORTANT AUTHORITY BOUNDARY:
-- the actual generator entries are not yet vendored in this repository.  This
-- owner pays source existence, exact representation IDs/files and the correct
-- group-theoretic role.  Same-basis recognition with `X6 + X6*` still requires
-- importing the matrices, computing their alternating form, and constructing a
-- symplectic change of basis to the repository standard form.
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
    repositorySymplecticBasisIntertwinerPaid : Bool
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
    false
    false

matrixAcquisitionBase : String
matrixAcquisitionBase =
  "ATLAS of Group Representations / 2.Suz:2 dim-12 GF(3) and Monster maximal subgroup 3^(1+12):6.Suz.2 dim-38 GF(3)"

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
    sameBasisX6PlusDualIntertwinerPaid : Bool
    sourceNativeHeisenbergConjugationPaid : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary true true true true true true false false false
