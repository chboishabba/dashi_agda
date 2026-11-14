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
-- The exact ATLAS bytes are acquired.  The inner 2.Suz pair determines a
-- unique nondegenerate alternating form; the direct outer generator has
-- multiplier 2=-1, while the second outer generator equals the inner second
-- generator.
--
-- Depth-five already produced a degree-six field-algebra selector.  Continuing
-- the exact same search through depth seven yields the stronger preferred word
--
--     g2^-1 g1 g2^-1 g1 g2 g1 g2^-1
--
-- with compression polynomial
--
--     x^6 - x^5 - x^4 - x^3 + x^2 - 1.
--
-- It has cyclic rank six, breaks swap01, and again does NOT stabilize X6.
-- PR #1105 locates a root gamma=(0,2,0,1,2,0) in the already-selected GF729,
-- proves gamma has multiplicative order 728, and constructs an explicit
-- invertible Q intertwining this compression with multiplication by gamma.
-- Thus the selected punctured field action is a single 728-orbit with trivial
-- stabilizer.  What remains open is the broader Monster semantic-action weld
-- and Agda-kernel certification of the concrete matrices.
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
selectedSourceWord = "g2^-1 g1 g2^-1 g1 g2 g1 g2^-1"

selectedSourceWordLength : Nat
selectedSourceWordLength = 7

selectedCompressionPolynomial : String
selectedCompressionPolynomial = "x^6 - x^5 - x^4 - x^3 + x^2 - 1"

selectedGF729PrimitiveRoot : String
selectedGF729PrimitiveRoot = "gamma = (0,2,0,1,2,0), multiplicative order 728"

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
    selectedGF729RootLocated : Bool
    selectedGF729RootPrimitive : Bool
    fieldGeneratorCandidate : Bool
open CompressionPolynomialReceipt public

canonicalCompressionPolynomialReceipt : CompressionPolynomialReceipt
canonicalCompressionPolynomialReceipt =
  compression-polynomial-receipt 7 true true true true true false true true true

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
    selectedGF729PrimitiveMultiplicativeGeneratorPaid : Bool
    selectedGF729PuncturedOrbit728Paid : Bool
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
    true
    true
    false
