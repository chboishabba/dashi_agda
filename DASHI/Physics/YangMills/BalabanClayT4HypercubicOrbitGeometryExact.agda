module DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- The generated normalized Brillouin grid has four interval cells per axis:
-- two inner and two outer.  The hypercubic signed-permutation action forgets
-- the signs and permutes the four axis positions, so its finite orbit invariant
-- is exactly the subset of axes which are outer.
--
-- We deliberately reuse the same Boolean four-cube carrier already used by
-- the Wilson/G2 Moebius decomposition.  Hence the 240 regular cells split by
-- outer-axis degree as
--
--       4 * 16 = 64,
--       6 * 16 = 96,
--       4 * 16 = 64,
--       1 * 16 = 16,
--
-- i.e. FOUR regular orbit types, not 240 unrelated box types.  The factor 16
-- is the independent choice of coordinate signs.  The theorem below is purely
-- generated finite geometry; no one-loop-integrand symmetry is assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.List.Base using (length)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube

outerFlag : Grid.IntervalCell → Bool
outerFlag Grid.negativeOuter = true
outerFlag Grid.negativeInner = false
outerFlag Grid.positiveInner = false
outerFlag Grid.positiveOuter = true

boolWeight : Bool → Nat
boolWeight false = zero
boolWeight true = suc zero

outerWeight : Grid.IntervalCell → Nat
outerWeight cell = boolWeight (outerFlag cell)

outerCount : Grid.GridCell4 → Nat
outerCount cell =
  outerWeight (Grid.c0 cell)
  + outerWeight (Grid.c1 cell)
  + outerWeight (Grid.c2 cell)
  + outerWeight (Grid.c3 cell)

-- The subset of coordinate positions carrying an outer interval.  This is the
-- same 16-element carrier used by the physical Wilson/G2 Moebius lane.
outerSubset : Grid.GridCell4 → Cube.Subset4
outerSubset cell
  with outerFlag (Grid.c0 cell)
     | outerFlag (Grid.c1 cell)
     | outerFlag (Grid.c2 cell)
     | outerFlag (Grid.c3 cell)
... | false | false | false | false = Cube.empty
... | true  | false | false | false = Cube.s0
... | false | true  | false | false = Cube.s1
... | false | false | true  | false = Cube.s2
... | false | false | false | true  = Cube.s3
... | true  | true  | false | false = Cube.s01
... | true  | false | true  | false = Cube.s02
... | true  | false | false | true  = Cube.s03
... | false | true  | true  | false = Cube.s12
... | false | true  | false | true  = Cube.s13
... | false | false | true  | true  = Cube.s23
... | true  | true  | true  | false = Cube.s012
... | true  | true  | false | true  = Cube.s013
... | true  | false | true  | true  = Cube.s023
... | false | true  | true  | true  = Cube.s123
... | true  | true  | true  | true  = Cube.s0123

outerSubsetCardinalityExact : ∀ cell →
  Cube.subsetCardinality (outerSubset cell) ≡ outerCount cell
outerSubsetCardinalityExact cell
  with outerFlag (Grid.c0 cell)
     | outerFlag (Grid.c1 cell)
     | outerFlag (Grid.c2 cell)
     | outerFlag (Grid.c3 cell)
... | false | false | false | false = refl
... | true  | false | false | false = refl
... | false | true  | false | false = refl
... | false | false | true  | false = refl
... | false | false | false | true  = refl
... | true  | true  | false | false = refl
... | true  | false | true  | false = refl
... | true  | false | false | true  = refl
... | false | true  | true  | false = refl
... | false | true  | false | true  = refl
... | false | false | true  | true  = refl
... | true  | true  | true  | false = refl
... | true  | true  | false | true  = refl
... | true  | false | true  | true  = refl
... | false | true  | true  | true  = refl
... | true  | true  | true  | true  = refl

data OrbitClass : Set where
  infrared oneOuter twoOuter threeOuter fourOuter : OrbitClass

orbitClass : Grid.GridCell4 → OrbitClass
orbitClass cell with outerCount cell
... | zero = infrared
... | suc zero = oneOuter
... | suc (suc zero) = twoOuter
... | suc (suc (suc zero)) = threeOuter
... | suc (suc (suc (suc _))) = fourOuter

sameOrbitClass : OrbitClass → OrbitClass → Bool
sameOrbitClass infrared infrared = true
sameOrbitClass oneOuter oneOuter = true
sameOrbitClass twoOuter twoOuter = true
sameOrbitClass threeOuter threeOuter = true
sameOrbitClass fourOuter fourOuter = true
sameOrbitClass _ _ = false

filterOrbit : OrbitClass → List Grid.GridCell4 → List Grid.GridCell4
filterOrbit selected [] = []
filterOrbit selected (cell ∷ cells) with sameOrbitClass selected (orbitClass cell)
... | true = cell ∷ filterOrbit selected cells
... | false = filterOrbit selected cells

infraredOrbitCells oneOuterCells twoOuterCells threeOuterCells fourOuterCells :
  List Grid.GridCell4
infraredOrbitCells = filterOrbit infrared Grid.allGridCells
oneOuterCells = filterOrbit oneOuter Grid.allGridCells
twoOuterCells = filterOrbit twoOuter Grid.allGridCells
threeOuterCells = filterOrbit threeOuter Grid.allGridCells
fourOuterCells = filterOrbit fourOuter Grid.allGridCells

infraredOrbitCellCount : length infraredOrbitCells ≡ 16
infraredOrbitCellCount = refl

oneOuterCellCount : length oneOuterCells ≡ 64
oneOuterCellCount = refl

twoOuterCellCount : length twoOuterCells ≡ 96
twoOuterCellCount = refl

threeOuterCellCount : length threeOuterCells ≡ 64
threeOuterCellCount = refl

fourOuterCellCount : length fourOuterCells ≡ 16
fourOuterCellCount = refl

regularOrbitMultiplicitySum :
  length oneOuterCells
  + (length twoOuterCells
  + (length threeOuterCells
  + length fourOuterCells))
  ≡ 240
regularOrbitMultiplicitySum = refl

-- The zero-outer orbit is definitionally the generated infrared family.  This
-- cross-checks the degree classifier against the independent allInner filter.
infraredOrbitMatchesGeneratedInfrared :
  infraredOrbitCells ≡ Grid.infraredGridCells
infraredOrbitMatchesGeneratedInfrared = refl

-- Canonical positive-sign representatives.  Proving the literal one-loop
-- scalar is invariant under the corresponding signed permutations is a
-- separate diagram theorem; once that is supplied only these four geometric
-- representatives need interval evaluation.
oneOuterRepresentative twoOuterRepresentative
  threeOuterRepresentative fourOuterRepresentative : Grid.GridCell4
oneOuterRepresentative =
  Grid.gridCell4 Grid.positiveOuter Grid.positiveInner
    Grid.positiveInner Grid.positiveInner
twoOuterRepresentative =
  Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter
    Grid.positiveInner Grid.positiveInner
threeOuterRepresentative =
  Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter
    Grid.positiveOuter Grid.positiveInner
fourOuterRepresentative =
  Grid.gridCell4 Grid.positiveOuter Grid.positiveOuter
    Grid.positiveOuter Grid.positiveOuter

oneOuterRepresentativeClass : orbitClass oneOuterRepresentative ≡ oneOuter
oneOuterRepresentativeClass = refl

twoOuterRepresentativeClass : orbitClass twoOuterRepresentative ≡ twoOuter
twoOuterRepresentativeClass = refl

threeOuterRepresentativeClass : orbitClass threeOuterRepresentative ≡ threeOuter
threeOuterRepresentativeClass = refl

fourOuterRepresentativeClass : orbitClass fourOuterRepresentative ≡ fourOuter
fourOuterRepresentativeClass = refl

brillouinOuterSubsetBridgeLevel : ProofLevel
brillouinOuterSubsetBridgeLevel = machineChecked

brillouinFourRegularOrbitCountLevel : ProofLevel
brillouinFourRegularOrbitCountLevel = machineChecked

-- Physical hypercubic invariance of the fully reduced scalar integrand remains
-- a diagram/source theorem, not a geometric assumption hidden in this module.
literalOneLoopHypercubicScalarInvarianceLevel : ProofLevel
literalOneLoopHypercubicScalarInvarianceLevel = conditional
