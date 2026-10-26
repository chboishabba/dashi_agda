module DASHI.Moonshine.Monster3BAtlasPrimitiveInertiaHeisenbergLiftReceiptExact where

------------------------------------------------------------------------
-- PRIMITIVE GF729 FIELD SELECTOR INSIDE THE CENTER-PRESERVING 3B LANE
--
-- Exact finite search over the acquired ATLAS 2.Suz:2 GF(3)^12 action finds
-- the depth-eight source word
--
--   g1 g2^-1 g1 g2 g1 g2^-1 g1 g2^-1
--
-- with THREE simultaneously useful properties:
--
-- 1. its full normalized 12x12 action has symplectic multiplier 1, so the
--    Heisenberg center is preserved rather than inverted;
-- 2. its X6 compression has irreducible degree-six polynomial and is explicitly
--    conjugate to multiplication by
--
--       gamma = (0,1,0,1,1,0)
--
--    in the already-selected GF(729), where gamma has multiplicative order 728;
-- 3. its asymmetric-cocycle defect D=M^T C M-C is symmetric of rank 12, hence
--    q(x)=2*x^T D*x supplies the exact quadratic central correction.
--
-- Thus one source word simultaneously pays the selected punctured-field
-- 728-orbit/trivial-stabilizer action and a center-preserving Heisenberg lift at
-- executable exact-matrix level.  By the pre-existing central-character
-- theorem, a genuine center-preserving realization acts within the chosen zeta
-- sector, unlike multiplier-2 outer words which exchange zeta and zeta^2.
--
-- It still does NOT construct the full phase-resolved Monster state carrier or
-- identify the Fin-90 multiplicity action.  Those remain the same-object seam.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import DASHI.Algebra.Trit using (neg; zer; pos)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Phase

record Matrix6 : Set where
  constructor matrix6
  field row0 row1 row2 row3 row4 row5 : G.X6
open Matrix6 public

preferredSourceWord : String
preferredSourceWord = "g1 g2^-1 g1 g2 g1 g2^-1 g1 g2^-1"

preferredSourceWordLength : Nat
preferredSourceWordLength = 8

preferredWordSymplecticMultiplier : Nat
preferredWordSymplecticMultiplier = 1

preferredCompression : Matrix6
preferredCompression = matrix6
  (G.x6 neg neg zer pos pos neg)
  (G.x6 zer zer zer pos pos neg)
  (G.x6 neg pos zer zer zer zer)
  (G.x6 pos neg zer neg neg neg)
  (G.x6 zer zer pos pos pos neg)
  (G.x6 zer zer pos neg pos pos)

selectedPrimitiveGamma : G.X6
selectedPrimitiveGamma = G.x6 zer pos zer pos pos zer

multiplicationByGamma : Matrix6
multiplicationByGamma = matrix6
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

selectedGammaMultiplicativeOrder : Nat
selectedGammaMultiplicativeOrder = 728

selectedPuncturedOrbitSize : Nat
selectedPuncturedOrbitSize = 728

selectedPuncturedStabilizerSize : Nat
selectedPuncturedStabilizerSize = 1

intertwinerDeterminantMod3 : Nat
intertwinerDeterminantMod3 = 2

cocycleDefectRank : Nat
cocycleDefectRank = 12

preferredWordPhaseImage : Phase.CentralPhase3
preferredWordPhaseImage = Phase.phaseZeta

runtimeReceiptPath : String
runtimeReceiptPath = "outputs/monster3b_atlas_compression_field_selector_20261012.json"

record Boundary : Set where
  constructor boundary
  field
    actualAtlasSourceWordPaid : Bool
    sourceWordStrictSymplecticPaid : Bool
    primitiveCompressionOrder728Paid : Bool
    selectedFieldIntertwinerRuntimePaid : Bool
    puncturedOrbit728Paid : Bool
    puncturedStabilizerTrivialPaid : Bool
    quadraticCentralCorrectionRuntimePaid : Bool
    selectedWordHeisenbergLiftRuntimePaid : Bool
    selectedWordCenterPreservingPaid : Bool
    genericCentralCharacterInertiaTheoremReusable : Bool
    actualPhaseResolvedMonsterSectorActionPaid : Bool
    fin90MultiplicityActionIdentified : Bool
    agdaKernelConcreteMatrixProofPaid : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary
    true true true true true true true true true true
    false false false
