module DASHI.Moonshine.OggSSPMonster3BSelectedGF729WeldExact where

------------------------------------------------------------------------
-- MONSTER-3B SOURCE COMPRESSION -> SELECTED GF(729) PRESENTATION
--
-- Cross-PR producer (#1098) now owns the exact ATLAS 2.Suz / 2.Suz:2 matrix
-- bytes and an executable receipt for the source word
--
--     g2 g1 g2^-1 g1 g2^-1.
--
-- After the unique inner alternating-form normalization, its translation-block
-- compression T has characteristic/minimal polynomial
--
--     p(x) = x^6 - x^5 - x^3 + x^2 + 1.
--
-- This branch already selected
--
--     GF(729) = F3[alpha] / (alpha^6 + alpha^5 + alpha^4 + 1).
--
-- The remaining presentation gap collapses by the literal affine generator
-- change
--
--     beta = 1 - alpha,
--
-- because over F3
--
--     f(1-x) = p(x).
--
-- The companion exact finite verifier constructs an invertible 6x6 matrix Q
-- with det(Q)=2 mod 3 satisfying
--
--     Q T = M_beta Q,
--
-- where M_beta is multiplication by beta in the already-selected polynomial
-- basis.  This is stronger than an order/cardinality match: it is an explicit
-- source-compression <-> selected-field generator conjugacy on F3^6.
--
-- AUTHORITY BOUNDARY:
-- the finite executable presentation weld is paid.  This owner records its
-- literal coordinates and provenance but does not rebrand the Python matrix
-- computation as an Agda-kernel proof.  Full Monster action/orbit/stabilizer
-- semantic recognition remains downstream.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G

record Matrix6 : Set where
  constructor matrix6
  field
    row0 row1 row2 row3 row4 row5 : G.X6
open Matrix6 public

compressionT : Matrix6
compressionT = matrix6
  (G.x6 zer neg pos zer neg pos)
  (G.x6 neg zer neg pos neg neg)
  (G.x6 zer zer zer zer pos neg)
  (G.x6 neg zer pos neg pos neg)
  (G.x6 neg zer neg neg zer neg)
  (G.x6 pos zer pos zer neg neg)

multiplicationByBeta : Matrix6
multiplicationByBeta = matrix6
  (G.x6 pos zer zer zer zer pos)
  (G.x6 neg pos zer zer zer zer)
  (G.x6 zer neg pos zer zer zer)
  (G.x6 zer zer neg pos zer zer)
  (G.x6 zer zer zer neg pos pos)
  (G.x6 zer zer zer zer neg neg)

intertwinerQ : Matrix6
intertwinerQ = matrix6
  (G.x6 pos zer zer neg pos pos)
  (G.x6 zer zer zer neg pos neg)
  (G.x6 zer zer neg pos zer pos)
  (G.x6 zer zer pos pos neg zer)
  (G.x6 zer pos pos zer pos neg)
  (G.x6 zer neg zer pos neg neg)

selectedFieldBeta : G.X6
selectedFieldBeta = G.x6 pos neg zer zer zer zer

swapBreakingWitness : G.X6
swapBreakingWitness = G.x6 pos zer zer zer zer zer

compressionOfSwapWitness : G.X6
compressionOfSwapWitness = G.x6 neg zer zer zer zer zer

swapOfCompressionWitness : G.X6
swapOfCompressionWitness = G.x6 neg zer zer neg neg pos

record DegreeSixPolynomial : Set where
  constructor degree-six-polynomial
  field
    c0 c1 c2 c3 c4 c5 c6 : Trit
open DegreeSixPolynomial public

selectedGF729Modulus : DegreeSixPolynomial
selectedGF729Modulus =
  degree-six-polynomial pos zer zer zer pos pos pos

compressionMinimalPolynomial : DegreeSixPolynomial
compressionMinimalPolynomial =
  degree-six-polynomial pos zer pos neg zer neg pos

sourceWord : String
sourceWord = "g2 g1 g2^-1 g1 g2^-1"

sourceProducerReceipt : String
sourceProducerReceipt =
  "PR #1098 outputs/monster3b_atlas_compression_field_selector_20261012.json"

selectedFieldVerifier : String
selectedFieldVerifier =
  "scripts/j369_monster3b_selected_gf729_weld.py"

selectedFieldReceipt : String
selectedFieldReceipt =
  "scripts/data/outputs/j369_field_transition_atlas_20261007/monster3bSelectedGF729Weld.json"

minimalPolynomialDegree : Nat
minimalPolynomialDegree = 6

cyclicSpanDimension : Nat
cyclicSpanDimension = 6

intertwinerDeterminantMod3 : Nat
intertwinerDeterminantMod3 = 2

record SelectedGF729WeldBoundary : Set where
  constructor selected-gf729-weld-boundary
  field
    actualAtlasMatrixBytesAcquired : Bool
    uniqueInnerAlternatingFormComputed : Bool
    outerSimilitudeMultiplierComputed : Bool
    degreeSixCompressionReceiptPaid : Bool
    swap01BrokenByCompression : Bool
    cyclicRankSixPaid : Bool
    affineBetaEqualsOneMinusAlphaLocated : Bool
    polynomialSubstitutionPaid : Bool
    explicitIntertwinerQComputed : Bool
    explicitIntertwinerQInvertible : Bool
    selectedGF729PresentationWeldPaid : Bool
    agdaKernelIntertwinerProofPaid : Bool
    fullActionOrbitStabilizerRecognitionPaid : Bool
open SelectedGF729WeldBoundary public

canonicalBoundary : SelectedGF729WeldBoundary
canonicalBoundary =
  selected-gf729-weld-boundary
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
    true
    false
    false
