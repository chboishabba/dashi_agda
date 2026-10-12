module DASHI.Moonshine.Monster3BAtlasCompressionFieldSelectionBoundaryExact where

------------------------------------------------------------------------
-- MONSTER-3B ATLAS SYMPLECTIC COMPRESSION FIELD-SELECTION MAX-CUT
--
-- The direct 12-dimensional GF(3) 2.Suz:2 module is absolutely irreducible,
-- so the full normalizer does not preserve the repository translation half X6.
-- That fact blocks a GLOBAL X6 submodule interpretation, but it does not block
-- field-selection by a source-derived compression.
--
-- Once the ATLAS action is welded to the repository polarization
--
--     Symplectic12 = X6 + X6*,
--
-- every same-basis linear source action g has the canonical translation block
--
--     A_g = pi_X o g o iota_X : X6 -> X6.
--
-- A_g is linear even when g mixes X6 and X6*.  Therefore requiring the source
-- word to stabilise X6 is unnecessary for the downstream K6 field-selector
-- experiment.  Stabilising words remain a stronger special case.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BAtlasSymplecticBasisIntertwinerCompilerExact as Atlas

embedTranslation : G.X6 → H.Symplectic12
embedTranslation x = H.symplectic12 x H.zeroX6

compression : Atlas.RepositorySymplecticAction → G.X6 → G.X6
compression action x =
  H.translationPart (Atlas.act action (embedTranslation x))

compressionPreservesAdd :
  (action : Atlas.RepositorySymplecticAction) →
  (x y : G.X6) →
  compression action (H.addX6 x y)
  ≡ H.addX6 (compression action x) (compression action y)
compressionPreservesAdd action x y
  rewrite Atlas.additive action (embedTranslation x) (embedTranslation y)
  = refl

record CompressionPolynomialReceipt : Set where
  constructor compression-polynomial-receipt
  field
    sourceWordLength : Nat
    characteristicPolynomialComputed : Bool
    minimalPolynomialComputed : Bool
    degreeSixIrreducible : Bool
    breaksRepositorySwap01 : Bool
    fieldGeneratorCandidate : Bool
open CompressionPolynomialReceipt public

record CompressionFieldSelectionBoundary : Set where
  constructor compression-field-selection-boundary
  field
    certifiedSymplecticTwelveSourceLocated : Bool
    concreteSourceMatricesImported : Bool
    sameBasisSymplecticWeldPaid : Bool
    everySameBasisActionHasCanonicalX6Compression : Bool
    compressionAdditivityPaidGenerically : Bool
    sourceWordMustStabiliseChosenX6 : Bool
    stabilizerSearchStillUsefulAsSpecialCase : Bool
    allWordCompressionPolynomialSearchInstalled : Bool
    actualDegreeSixCompressionCandidateFound : Bool
    downstreamGF729SameObjectRecognitionPaid : Bool
open CompressionFieldSelectionBoundary public

canonicalCompressionFieldSelectionBoundary : CompressionFieldSelectionBoundary
canonicalCompressionFieldSelectionBoundary =
  compression-field-selection-boundary
    true
    false
    false
    true
    true
    false
    true
    true
    false
    false
