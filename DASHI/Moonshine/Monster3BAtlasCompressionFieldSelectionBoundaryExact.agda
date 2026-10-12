module DASHI.Moonshine.Monster3BAtlasCompressionFieldSelectionBoundaryExact where

------------------------------------------------------------------------
-- MONSTER-3B ATLAS COMPRESSION FIELD-SELECTION MAX-CUT
--
-- The absolutely irreducible 12-dimensional GF(3) 2.Suz:2 source does not
-- preserve the repository translation half X6 globally.  The correct source
-- observable is therefore the canonical compression
--
--     A_g = pi_X o g o iota_X : X6 -> X6
--
-- after the same-basis 12-dimensional weld.
--
-- The exact ATLAS bytes are now acquired.  The inner 2.Suz pair determines a
-- unique nondegenerate alternating form; the direct outer generator has
-- multiplier 2=-1, while the second outer generator equals the inner second
-- generator.  Searching the concrete outer source action through depth five
-- finds a source word
--
--     g2 g1 g2^-1 g1 g2^-1
--
-- whose X6 compression has irreducible degree-six polynomial
--
--     x^6 - x^5 - x^3 + x^2 + 1,
--
-- cyclic rank six from e0, and breaks the repository swap01 symmetry.  It does
-- not stabilise X6, which is precisely why the compression recut is stronger
-- than the obsolete stabilizer-only search.
--
-- PR #1105 independently welds this polynomial to its already-selected GF729
-- model by beta=1-alpha and an explicit invertible 6x6 conjugacy.  That pays a
-- finite field-presentation same-object weld, not the entire Monster
-- multiplicative action/orbit/stabilizer semantics and not an Agda matrix proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

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

selectedSourceWord : String
selectedSourceWord = "g2 g1 g2^-1 g1 g2^-1"

selectedSourceWordLength : Nat
selectedSourceWordLength = 5

selectedCompressionPolynomial : String
selectedCompressionPolynomial = "x^6 - x^5 - x^3 + x^2 + 1"

selectedGF729GeneratorChange : String
selectedGF729GeneratorChange = "beta = 1 - alpha"

record CompressionPolynomialReceipt : Set where
  constructor compression-polynomial-receipt
  field
    sourceWordLength : Nat
    characteristicPolynomialComputed : Bool
    minimalPolynomialComputed : Bool
    degreeSixIrreducible : Bool
    cyclicRankSix : Bool
    breaksRepositorySwap01 : Bool
    stabilisesTranslationLagrangian : Bool
    fieldGeneratorCandidate : Bool
open CompressionPolynomialReceipt public

canonicalCompressionPolynomialReceipt : CompressionPolynomialReceipt
canonicalCompressionPolynomialReceipt =
  compression-polynomial-receipt 5 true true true true true false true

record CompressionFieldSelectionBoundary : Set where
  constructor compression-field-selection-boundary
  field
    certifiedSymplecticTwelveSourceLocated : Bool
    concreteSourceMatricesImported : Bool
    innerAlternatingFormRuntimePaid : Bool
    outerSimilitudeMultiplierRuntimePaid : Bool
    sameBasisSymplecticWeldRuntimePaid : Bool
    sameBasisSymplecticWeldKernelPaid : Bool
    everySameBasisActionHasCanonicalX6Compression : Bool
    compressionAdditivityPaidGenerically : Bool
    sourceWordMustStabiliseChosenX6 : Bool
    allWordCompressionPolynomialSearchInstalled : Bool
    actualDegreeSixCompressionCandidateFound : Bool
    actualCyclicRankSixPaid : Bool
    actualSwapBreakingPaid : Bool
    selectedGF729PresentationWeldRuntimePaid : Bool
    fullMonsterActionOrbitStabilizerRecognitionPaid : Bool
open CompressionFieldSelectionBoundary public

canonicalCompressionFieldSelectionBoundary : CompressionFieldSelectionBoundary
canonicalCompressionFieldSelectionBoundary =
  compression-field-selection-boundary
    true
    true
    true
    true
    true
    false
    true
    true
    false
    true
    true
    true
    true
    true
    false
