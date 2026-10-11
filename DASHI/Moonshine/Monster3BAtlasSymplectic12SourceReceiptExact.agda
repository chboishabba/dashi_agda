module DASHI.Moonshine.Monster3BAtlasSymplectic12SourceReceiptExact where

------------------------------------------------------------------------
-- ATLAS / CTblLib SOURCE RECEIPT FOR THE 3B NORMALIZER SYMPLECTIC 12-MODULE
--
-- External executable source:
--   Thomas Breuer, Kay Magaard, Robert A. Wilson,
--   "Some steps in the verification of the ordinary character table of the
--   Monster group" (2024), Appendix 9, especially Section 9.2.
--
-- The documented ATLAS representation is a faithful 38-dimensional GF(3)
-- representation of
--
--     H = 3^(1+12) : 6.Suz.2
--
-- with generator matrix files
--
--     M3max7G0-f3r38B0.m1 ... M3max7G0-f3r38B0.m4.
--
-- The matrices are block diagonal of sizes 24 and 14.  The lower-right 14x14
-- blocks generate
--
--     H/X ~= 3_+^(1+12) : 2.Suz.2.
--
-- The source explicitly states that the 12-dimensional irreducible
-- representation of 2.Suz.2 over GF(3) preserves a symplectic form and embeds
-- 2.Suz.2 in Sp(12,3), the automorphism group of the extraspecial
-- 3_+^(1+12).  Thus the source-side quotient action needed by the repository's
-- Heisenberg normalizer compiler genuinely exists.
--
-- IMPORTANT AUTHORITY BOUNDARY:
-- the actual matrix entries have not yet been imported into this repository.
-- Therefore this file pays SOURCE EXISTENCE and exact acquisition coordinates,
-- not a same-basis intertwiner to the repository's X6 + X6* convention.
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
    false
    false

matrixAcquisitionBase : String
matrixAcquisitionBase =
  "ATLAS of Group Representations / Monster maximal subgroup 3^(1+12):6.Suz.2"

record Boundary : Set where
  constructor boundary
  field
    certifiedAtlasRepresentationLocated : Bool
    exactGeneratorFileNamesKnown : Bool
    sourceSymplectic12ActionExists : Bool
    sourceEmbedsNormalizerQuotientInSp12_3 : Bool
    sourceExplainsActionOnExtraspecialQuotient : Bool
    rawMatrixEntriesInRepo : Bool
    sameBasisX6PlusDualIntertwinerPaid : Bool
    sourceNativeHeisenbergConjugationPaid : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary true true true true true false false false
