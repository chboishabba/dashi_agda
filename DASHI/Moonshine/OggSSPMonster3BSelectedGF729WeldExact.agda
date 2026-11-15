module DASHI.Moonshine.OggSSPMonster3BSelectedGF729WeldExact where

------------------------------------------------------------------------
-- MONSTER-3B SOURCE COMPRESSIONS -> SELECTED GF(729) ACTION
--
-- Cross-PR producer #1098 owns the exact ATLAS 2.Suz / 2.Suz:2 GF(3)^12
-- bytes, the unique inner alternating-form normalization and literal source
-- compression matrices.  This owner consumes the exact selected-field verifier
--
--   scripts/j369_monster3b_selected_gf729_weld.py
--
-- which now keeps three source roles separate:
--
-- 1. depth 5, multiplier 1:
--      beta=1-alpha, order 364;
--    first selected-field presentation weld;
--
-- 2. depth 7, multiplier 2:
--      gamma=(0,2,0,1,2,0), order 728;
--    primitive center-INVERTING/similitude comparator;
--
-- 3. depth 8, multiplier 1:
--      delta=(0,1,0,1,1,0), order 728;
--    preferred CENTER-PRESERVING primitive target.
--
-- The depth-eight compression has polynomial
--
--   x^6 - x^4 + x^2 - x - 1
--
-- and exact finite execution constructs invertible Q, det(Q)=2 mod 3, with
--
--   Q T = M_delta Q.
--
-- Therefore one source-derived STRICT-symplectic word acts, after the explicit
-- same-object basis change, as multiplication by a primitive element of the
-- already-selected GF(729).  Its powers give one 728-element orbit on the
-- punctured field and trivial stabilizer while remaining eligible for a fixed
-- central-character/Heisenberg phase sector.
--
-- This pays the finite selected-field multiplicative-action weld.  It does NOT
-- identify the broader phase-resolved Monster state, Fin-90 multiplicity action,
-- or constitute an Agda-kernel replay of the literal matrix equations.
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

record DegreeSixPolynomial : Set where
  constructor degree-six-polynomial
  field
    c0 c1 c2 c3 c4 c5 c6 : Trit
open DegreeSixPolynomial public

selectedGF729Modulus : DegreeSixPolynomial
selectedGF729Modulus = degree-six-polynomial pos zer zer zer pos pos pos

------------------------------------------------------------------------
-- Stage 1 provenance: first strict field-algebra weld.
------------------------------------------------------------------------

earlierBetaSourceWord : String
earlierBetaSourceWord = "g2 g1 g2^-1 g1 g2^-1"

earlierSelectedFieldBeta : G.X6
earlierSelectedFieldBeta = G.x6 pos neg zer zer zer zer

earlierBetaMultiplicativeOrder : Nat
earlierBetaMultiplicativeOrder = 364

------------------------------------------------------------------------
-- Stage 2: primitive center-inverting comparator (multiplier 2).
------------------------------------------------------------------------

inverterSourceWord : String
inverterSourceWord = "g2^-1 g1 g2^-1 g1 g2 g1 g2^-1"

inverterFieldGamma : G.X6
inverterFieldGamma = G.x6 zer neg zer pos neg zer

inverterMultiplicativeOrder : Nat
inverterMultiplicativeOrder = 728

inverterSimilitudeMultiplier : Nat
inverterSimilitudeMultiplier = 2

------------------------------------------------------------------------
-- Stage 3: preferred center-preserving primitive compression (multiplier 1).
------------------------------------------------------------------------

compressionT : Matrix6
compressionT = matrix6
  (G.x6 neg neg zer pos pos neg)
  (G.x6 zer zer zer pos pos neg)
  (G.x6 neg pos zer zer zer zer)
  (G.x6 pos neg zer neg neg neg)
  (G.x6 zer zer pos pos pos neg)
  (G.x6 zer zer pos neg pos pos)

multiplicationByDelta : Matrix6
multiplicationByDelta = matrix6
  (G.x6 zer zer neg zer pos pos)
  (G.x6 pos zer zer neg zer pos)
  (G.x6 zer pos zer zer neg zer)
  (G.x6 pos zer pos zer zer neg)
  (G.x6 pos pos neg pos pos pos)
  (G.x6 zer pos zer neg neg neg)

intertwinerQ : Matrix6
intertwinerQ = matrix6
  (G.x6 pos pos zer pos zer zer)
  (G.x6 zer neg zer pos neg neg)
  (G.x6 zer zer pos pos zer pos)
  (G.x6 zer pos pos neg zer neg)
  (G.x6 zer neg neg zer neg neg)
  (G.x6 zer neg neg neg neg neg)

selectedFieldDelta : G.X6
selectedFieldDelta = G.x6 zer pos zer pos pos zer

compressionMinimalPolynomial : DegreeSixPolynomial
compressionMinimalPolynomial =
  degree-six-polynomial neg neg pos zer neg zer pos

sourceWord : String
sourceWord = "g1 g2^-1 g1 g2 g1 g2^-1 g1 g2^-1"

sourceWordLength : Nat
sourceWordLength = 8

sourceSimilitudeMultiplier : Nat
sourceSimilitudeMultiplier = 1

minimalPolynomialDegree : Nat
minimalPolynomialDegree = 6

cyclicSpanDimension : Nat
cyclicSpanDimension = 6

selectedDeltaMultiplicativeOrder : Nat
selectedDeltaMultiplicativeOrder = 728

puncturedOrbitSize : Nat
puncturedOrbitSize = 728

puncturedStabilizerSize : Nat
puncturedStabilizerSize = 1

intertwinerDeterminantMod3 : Nat
intertwinerDeterminantMod3 = 2

sourceProducerReceipt : String
sourceProducerReceipt =
  "PR #1098 outputs/monster3b_atlas_compression_field_selector_20261012.json"

selectedFieldVerifier : String
selectedFieldVerifier = "scripts/j369_monster3b_selected_gf729_weld.py"

selectedFieldReceipt : String
selectedFieldReceipt =
  "scripts/data/outputs/j369_field_transition_atlas_20261007/monster3bSelectedGF729Weld.json"

record SelectedGF729WeldBoundary : Set where
  constructor selected-gf729-weld-boundary
  field
    actualAtlasMatrixBytesAcquired : Bool
    uniqueInnerAlternatingFormComputed : Bool
    outerSimilitudeMultiplierComputed : Bool
    earlierBetaPresentationWeldPaid : Bool
    primitiveInverterComparatorPaid : Bool
    centerPreservingPrimitiveCompressionPaid : Bool
    degreeSixCompressionReceiptPaid : Bool
    swap01BrokenByCompression : Bool
    cyclicRankSixPaid : Bool
    selectedGF729PrimitiveRootLocated : Bool
    selectedGF729PrimitiveOrder728Paid : Bool
    explicitIntertwinerQComputed : Bool
    explicitIntertwinerQInvertible : Bool
    selectedGF729PresentationWeldPaid : Bool
    selectedGF729MultiplicativeActionWeldPaid : Bool
    centerPreservingPrimitiveActionWeldPaid : Bool
    selectedGF729PuncturedOrbit728Paid : Bool
    selectedGF729PuncturedStabilizerTrivialPaid : Bool
    agdaKernelIntertwinerProofPaid : Bool
    fullMonsterSemanticActionRecognitionPaid : Bool
open SelectedGF729WeldBoundary public

canonicalBoundary : SelectedGF729WeldBoundary
canonicalBoundary =
  selected-gf729-weld-boundary
    true true true
    true true true
    true true true
    true true
    true true
    true true true
    true true
    false false
