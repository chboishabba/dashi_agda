module DASHI.Physics.YangMills.BalabanClayT4HyperoctahedralGridOrbitExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Hermann Weyl,
-- "The Classical Groups: Their Invariants and Representations",
-- Princeton University Press, 1939/1946. No DOI assigned.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Put the generated 4^4 Brillouin grid under the literal signed-coordinate
-- and adjacent-coordinate-swap generators of B4 = (C2)^4 semidirect S4.
-- The geometric orbit invariant is the number of outer coordinates.  On the
-- exact generated grid this gives
--
--      outer rank 0 : 16 cells   (the infrared cube),
--      outer rank 1 : 64 cells,
--      outer rank 2 : 96 cells,
--      outer rank 3 : 64 cells,
--      outer rank 4 : 16 cells.
--
-- Hence the 240 regular cells split geometrically as 64+96+64+16.  We also
-- record the more conservative axis-0 stabilizer split: if an external
-- momentum singles out axis 0, the remaining S3 geometry has seven regular
-- classes with counts 48,48,16,16,48,48,16.  This makes the full-B4 versus
-- fixed-external-momentum distinction explicit instead of silently assuming
-- 240 -> 4 for the physical scalar integrand.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (length)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid

outer : Grid.IntervalCell → Bool
outer Grid.negativeOuter = true
outer Grid.negativeInner = false
outer Grid.positiveInner = false
outer Grid.positiveOuter = true

flipInterval : Grid.IntervalCell → Grid.IntervalCell
flipInterval Grid.negativeOuter = Grid.positiveOuter
flipInterval Grid.negativeInner = Grid.positiveInner
flipInterval Grid.positiveInner = Grid.negativeInner
flipInterval Grid.positiveOuter = Grid.negativeOuter

flipIntervalInvolutive : ∀ interval → flipInterval (flipInterval interval) ≡ interval
flipIntervalInvolutive Grid.negativeOuter = refl
flipIntervalInvolutive Grid.negativeInner = refl
flipIntervalInvolutive Grid.positiveInner = refl
flipIntervalInvolutive Grid.positiveOuter = refl

outerFlipExact : ∀ interval → outer (flipInterval interval) ≡ outer interval
outerFlipExact Grid.negativeOuter = refl
outerFlipExact Grid.negativeInner = refl
outerFlipExact Grid.positiveInner = refl
outerFlipExact Grid.positiveOuter = refl

data GeometricOrbit : Set where
  infrared rank1 rank2 rank3 rank4 : GeometricOrbit

rank4Bits : Bool → Bool → Bool → Bool → GeometricOrbit
rank4Bits false false false false = infrared
rank4Bits true  false false false = rank1
rank4Bits false true  false false = rank1
rank4Bits false false true  false = rank1
rank4Bits false false false true  = rank1
rank4Bits true  true  false false = rank2
rank4Bits true  false true  false = rank2
rank4Bits true  false false true  = rank2
rank4Bits false true  true  false = rank2
rank4Bits false true  false true  = rank2
rank4Bits false false true  true  = rank2
rank4Bits false true  true  true  = rank3
rank4Bits true  false true  true  = rank3
rank4Bits true  true  false true  = rank3
rank4Bits true  true  true  false = rank3
rank4Bits true  true  true  true  = rank4

geometricOrbit : Grid.GridCell4 → GeometricOrbit
geometricOrbit cell = rank4Bits
  (outer (Grid.c0 cell)) (outer (Grid.c1 cell))
  (outer (Grid.c2 cell)) (outer (Grid.c3 cell))

rank4Swap01 : ∀ a b c d → rank4Bits a b c d ≡ rank4Bits b a c d
rank4Swap01 true true c d = refl
rank4Swap01 false false c d = refl
rank4Swap01 true false false false = refl
rank4Swap01 true false false true = refl
rank4Swap01 true false true false = refl
rank4Swap01 true false true true = refl
rank4Swap01 false true false false = refl
rank4Swap01 false true false true = refl
rank4Swap01 false true true false = refl
rank4Swap01 false true true true = refl

rank4Swap12 : ∀ a b c d → rank4Bits a b c d ≡ rank4Bits a c b d
rank4Swap12 a true true d = refl
rank4Swap12 a false false d = refl
rank4Swap12 false true false false = refl
rank4Swap12 false true false true = refl
rank4Swap12 true true false false = refl
rank4Swap12 true true false true = refl
rank4Swap12 false false true false = refl
rank4Swap12 false false true true = refl
rank4Swap12 true false true false = refl
rank4Swap12 true false true true = refl

rank4Swap23 : ∀ a b c d → rank4Bits a b c d ≡ rank4Bits a b d c
rank4Swap23 a b true true = refl
rank4Swap23 a b false false = refl
rank4Swap23 false false true false = refl
rank4Swap23 false true true false = refl
rank4Swap23 true false true false = refl
rank4Swap23 true true true false = refl
rank4Swap23 false false false true = refl
rank4Swap23 false true false true = refl
rank4Swap23 true false false true = refl
rank4Swap23 true true false true = refl

data HyperoctahedralGenerator : Set where
  identity flip0 flip1 flip2 flip3 swap01 swap12 swap23 : HyperoctahedralGenerator

act : HyperoctahedralGenerator → Grid.GridCell4 → Grid.GridCell4
act identity cell = cell
act flip0 (Grid.gridCell4 a b c d) = Grid.gridCell4 (flipInterval a) b c d
act flip1 (Grid.gridCell4 a b c d) = Grid.gridCell4 a (flipInterval b) c d
act flip2 (Grid.gridCell4 a b c d) = Grid.gridCell4 a b (flipInterval c) d
act flip3 (Grid.gridCell4 a b c d) = Grid.gridCell4 a b c (flipInterval d)
act swap01 (Grid.gridCell4 a b c d) = Grid.gridCell4 b a c d
act swap12 (Grid.gridCell4 a b c d) = Grid.gridCell4 a c b d
act swap23 (Grid.gridCell4 a b c d) = Grid.gridCell4 a b d c

geometricOrbitInvariant : ∀ generator cell →
  geometricOrbit (act generator cell) ≡ geometricOrbit cell
geometricOrbitInvariant identity cell = refl
geometricOrbitInvariant flip0 (Grid.gridCell4 a b c d)
  rewrite outerFlipExact a = refl
geometricOrbitInvariant flip1 (Grid.gridCell4 a b c d)
  rewrite outerFlipExact b = refl
geometricOrbitInvariant flip2 (Grid.gridCell4 a b c d)
  rewrite outerFlipExact c = refl
geometricOrbitInvariant flip3 (Grid.gridCell4 a b c d)
  rewrite outerFlipExact d = refl
geometricOrbitInvariant swap01 (Grid.gridCell4 a b c d) =
  rank4Swap01 (outer a) (outer b) (outer c) (outer d)
geometricOrbitInvariant swap12 (Grid.gridCell4 a b c d) =
  rank4Swap12 (outer a) (outer b) (outer c) (outer d)
geometricOrbitInvariant swap23 (Grid.gridCell4 a b c d) =
  rank4Swap23 (outer a) (outer b) (outer c) (outer d)

infixr 5 _++_
_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ right = right
(x ∷ xs) ++ right = x ∷ (xs ++ right)

filterOrbit : GeometricOrbit → List Grid.GridCell4 → List Grid.GridCell4
filterOrbit target [] = []
filterOrbit target (cell ∷ cells) with geometricOrbit cell | target
... | infrared | infrared = cell ∷ filterOrbit target cells
... | rank1 | rank1 = cell ∷ filterOrbit target cells
... | rank2 | rank2 = cell ∷ filterOrbit target cells
... | rank3 | rank3 = cell ∷ filterOrbit target cells
... | rank4 | rank4 = cell ∷ filterOrbit target cells
... | _ | _ = filterOrbit target cells

infraredOrbitCells rank1Cells rank2Cells rank3Cells rank4Cells : List Grid.GridCell4
infraredOrbitCells = filterOrbit infrared Grid.allGridCells
rank1Cells = filterOrbit rank1 Grid.allGridCells
rank2Cells = filterOrbit rank2 Grid.allGridCells
rank3Cells = filterOrbit rank3 Grid.allGridCells
rank4Cells = filterOrbit rank4 Grid.allGridCells

infraredOrbitCountExact : length infraredOrbitCells ≡ 16
infraredOrbitCountExact = refl
rank1CountExact : length rank1Cells ≡ 64
rank1CountExact = refl
rank2CountExact : length rank2Cells ≡ 96
rank2CountExact = refl
rank3CountExact : length rank3Cells ≡ 64
rank3CountExact = refl
rank4CountExact : length rank4Cells ≡ 16
rank4CountExact = refl
regularOrbitCountDecompositionExact :
  length rank1Cells + length rank2Cells + length rank3Cells + length rank4Cells ≡ 240
regularOrbitCountDecompositionExact = refl

------------------------------------------------------------------------
-- Fixed-axis stabilizer geometry.
------------------------------------------------------------------------

data TransverseRank : Set where t0 t1 t2 t3 : TransverseRank

rank3Bits : Bool → Bool → Bool → TransverseRank
rank3Bits false false false = t0
rank3Bits true false false = t1
rank3Bits false true false = t1
rank3Bits false false true = t1
rank3Bits true true false = t2
rank3Bits true false true = t2
rank3Bits false true true = t2
rank3Bits true true true = t3

data Axis0Orbit : Set where
  a0t0 a0t1 a0t2 a0t3 a1t0 a1t1 a1t2 a1t3 : Axis0Orbit

axis0Orbit : Grid.GridCell4 → Axis0Orbit
axis0Orbit cell with outer (Grid.c0 cell) | rank3Bits (outer (Grid.c1 cell)) (outer (Grid.c2 cell)) (outer (Grid.c3 cell))
... | false | t0 = a0t0
... | false | t1 = a0t1
... | false | t2 = a0t2
... | false | t3 = a0t3
... | true | t0 = a1t0
... | true | t1 = a1t1
... | true | t2 = a1t2
... | true | t3 = a1t3

filterAxisOrbit : Axis0Orbit → List Grid.GridCell4 → List Grid.GridCell4
filterAxisOrbit target [] = []
filterAxisOrbit target (cell ∷ cells) with axis0Orbit cell | target
... | a0t0 | a0t0 = cell ∷ filterAxisOrbit target cells
... | a0t1 | a0t1 = cell ∷ filterAxisOrbit target cells
... | a0t2 | a0t2 = cell ∷ filterAxisOrbit target cells
... | a0t3 | a0t3 = cell ∷ filterAxisOrbit target cells
... | a1t0 | a1t0 = cell ∷ filterAxisOrbit target cells
... | a1t1 | a1t1 = cell ∷ filterAxisOrbit target cells
... | a1t2 | a1t2 = cell ∷ filterAxisOrbit target cells
... | a1t3 | a1t3 = cell ∷ filterAxisOrbit target cells
... | _ | _ = filterAxisOrbit target cells

axis0InfraredCells axis0t1Cells axis0t2Cells axis0t3Cells : List Grid.GridCell4
axis1t0Cells axis1t1Cells axis1t2Cells axis1t3Cells : List Grid.GridCell4
axis0InfraredCells = filterAxisOrbit a0t0 Grid.allGridCells
axis0t1Cells = filterAxisOrbit a0t1 Grid.allGridCells
axis0t2Cells = filterAxisOrbit a0t2 Grid.allGridCells
axis0t3Cells = filterAxisOrbit a0t3 Grid.allGridCells
axis1t0Cells = filterAxisOrbit a1t0 Grid.allGridCells
axis1t1Cells = filterAxisOrbit a1t1 Grid.allGridCells
axis1t2Cells = filterAxisOrbit a1t2 Grid.allGridCells
axis1t3Cells = filterAxisOrbit a1t3 Grid.allGridCells

axis0InfraredCountExact : length axis0InfraredCells ≡ 16
axis0InfraredCountExact = refl
axis0t1CountExact : length axis0t1Cells ≡ 48
axis0t1CountExact = refl
axis0t2CountExact : length axis0t2Cells ≡ 48
axis0t2CountExact = refl
axis0t3CountExact : length axis0t3Cells ≡ 16
axis0t3CountExact = refl
axis1t0CountExact : length axis1t0Cells ≡ 16
axis1t0CountExact = refl
axis1t1CountExact : length axis1t1Cells ≡ 48
axis1t1CountExact = refl
axis1t2CountExact : length axis1t2Cells ≡ 48
axis1t2CountExact = refl
axis1t3CountExact : length axis1t3Cells ≡ 16
axis1t3CountExact = refl
axis0RegularStabilizerCountExact :
  length axis0t1Cells + length axis0t2Cells + length axis0t3Cells +
  length axis1t0Cells + length axis1t1Cells + length axis1t2Cells + length axis1t3Cells ≡ 240
axis0RegularStabilizerCountExact = refl

hyperoctahedralGridGeneratorActionLevel : ProofLevel
hyperoctahedralGridGeneratorActionLevel = machineChecked

regularFourOrbitClassificationLevel : ProofLevel
regularFourOrbitClassificationLevel = machineChecked

fixedAxisSevenOrbitClassificationLevel : ProofLevel
fixedAxisSevenOrbitClassificationLevel = machineChecked
