module DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Hermann Weyl,
-- "The Classical Groups: Their Invariants and Representations", Princeton
-- University Press, second edition, 1946. No DOI assigned.
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
-- Construct, rather than merely name, the finite signed-permutation action on
-- the generated 4^4 normalized Brillouin grid. Four coordinate sign flips and
-- the three adjacent transpositions generate the hyperoctahedral action B_4.
--
-- We prove:
--   * every generator is an involution;
--   * the number of outer coordinates is invariant under every generator;
--   * every grid cell has a generated path to the canonical representative
--     with the same outer count.
--
-- Hence the 240 regular cells really have only four generated orbit types
-- (1,2,3,4 outer axes), rather than this being inferred from cardinalities.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HypercubicOrbitGeometryExact as Orbit

flipInterval : Grid.IntervalCell → Grid.IntervalCell
flipInterval Grid.negativeOuter = Grid.positiveOuter
flipInterval Grid.negativeInner = Grid.positiveInner
flipInterval Grid.positiveInner = Grid.negativeInner
flipInterval Grid.positiveOuter = Grid.negativeOuter

flipIntervalInvolutive : ∀ cell → flipInterval (flipInterval cell) ≡ cell
flipIntervalInvolutive Grid.negativeOuter = refl
flipIntervalInvolutive Grid.negativeInner = refl
flipIntervalInvolutive Grid.positiveInner = refl
flipIntervalInvolutive Grid.positiveOuter = refl

outerWeightFlipInvariant : ∀ cell →
  Orbit.outerWeight (flipInterval cell) ≡ Orbit.outerWeight cell
outerWeightFlipInvariant Grid.negativeOuter = refl
outerWeightFlipInvariant Grid.negativeInner = refl
outerWeightFlipInvariant Grid.positiveInner = refl
outerWeightFlipInvariant Grid.positiveOuter = refl

data HypercubicGenerator : Set where
  flip0 flip1 flip2 flip3 swap01 swap12 swap23 : HypercubicGenerator

act : HypercubicGenerator → Grid.GridCell4 → Grid.GridCell4
act flip0 cell =
  Grid.gridCell4 (flipInterval (Grid.c0 cell))
    (Grid.c1 cell) (Grid.c2 cell) (Grid.c3 cell)
act flip1 cell =
  Grid.gridCell4 (Grid.c0 cell)
    (flipInterval (Grid.c1 cell)) (Grid.c2 cell) (Grid.c3 cell)
act flip2 cell =
  Grid.gridCell4 (Grid.c0 cell) (Grid.c1 cell)
    (flipInterval (Grid.c2 cell)) (Grid.c3 cell)
act flip3 cell =
  Grid.gridCell4 (Grid.c0 cell) (Grid.c1 cell) (Grid.c2 cell)
    (flipInterval (Grid.c3 cell))
act swap01 cell =
  Grid.gridCell4 (Grid.c1 cell) (Grid.c0 cell) (Grid.c2 cell) (Grid.c3 cell)
act swap12 cell =
  Grid.gridCell4 (Grid.c0 cell) (Grid.c2 cell) (Grid.c1 cell) (Grid.c3 cell)
act swap23 cell =
  Grid.gridCell4 (Grid.c0 cell) (Grid.c1 cell) (Grid.c3 cell) (Grid.c2 cell)

generatorInvolutive : ∀ generator cell →
  act generator (act generator cell) ≡ cell
generatorInvolutive flip0 (Grid.gridCell4 a b c d)
  rewrite flipIntervalInvolutive a = refl
generatorInvolutive flip1 (Grid.gridCell4 a b c d)
  rewrite flipIntervalInvolutive b = refl
generatorInvolutive flip2 (Grid.gridCell4 a b c d)
  rewrite flipIntervalInvolutive c = refl
generatorInvolutive flip3 (Grid.gridCell4 a b c d)
  rewrite flipIntervalInvolutive d = refl
generatorInvolutive swap01 (Grid.gridCell4 a b c d) = refl
generatorInvolutive swap12 (Grid.gridCell4 a b c d) = refl
generatorInvolutive swap23 (Grid.gridCell4 a b c d) = refl

outerCountGeneratorInvariant : ∀ generator cell →
  Orbit.outerCount (act generator cell) ≡ Orbit.outerCount cell
outerCountGeneratorInvariant flip0 (Grid.gridCell4 a b c d)
  rewrite outerWeightFlipInvariant a = refl
outerCountGeneratorInvariant flip1 (Grid.gridCell4 a b c d)
  rewrite outerWeightFlipInvariant b = refl
outerCountGeneratorInvariant flip2 (Grid.gridCell4 a b c d)
  rewrite outerWeightFlipInvariant c = refl
outerCountGeneratorInvariant flip3 (Grid.gridCell4 a b c d)
  rewrite outerWeightFlipInvariant d = refl
outerCountGeneratorInvariant swap01 (Grid.gridCell4 a b c d) =
  cong (λ prefix → prefix + Orbit.outerWeight c + Orbit.outerWeight d)
    (+-comm (Orbit.outerWeight b) (Orbit.outerWeight a))
outerCountGeneratorInvariant swap12 (Grid.gridCell4 a b c d) =
  trans
    (sym (+-assoc (Orbit.outerWeight a) (Orbit.outerWeight c)
      (Orbit.outerWeight b)))
    (trans
      (cong (λ middle → middle + Orbit.outerWeight d)
        (trans
          (+-assoc (Orbit.outerWeight a) (Orbit.outerWeight c)
            (Orbit.outerWeight b))
          (trans
            (cong (Orbit.outerWeight a +_)
              (+-comm (Orbit.outerWeight c) (Orbit.outerWeight b)))
            (sym (+-assoc (Orbit.outerWeight a) (Orbit.outerWeight b)
              (Orbit.outerWeight c))))))
      refl)
outerCountGeneratorInvariant swap23 (Grid.gridCell4 a b c d) =
  cong (λ tail → Orbit.outerWeight a + Orbit.outerWeight b + tail)
    (+-comm (Orbit.outerWeight d) (Orbit.outerWeight c))

classFromCount : Nat → Orbit.OrbitClass
classFromCount zero = Orbit.infrared
classFromCount (suc zero) = Orbit.oneOuter
classFromCount (suc (suc zero)) = Orbit.twoOuter
classFromCount (suc (suc (suc zero))) = Orbit.threeOuter
classFromCount (suc (suc (suc (suc _)))) = Orbit.fourOuter

orbitClassAsCount : ∀ cell →
  Orbit.orbitClass cell ≡ classFromCount (Orbit.outerCount cell)
orbitClassAsCount cell with Orbit.outerCount cell
... | zero = refl
... | suc zero = refl
... | suc (suc zero) = refl
... | suc (suc (suc zero)) = refl
... | suc (suc (suc (suc n))) = refl

orbitClassGeneratorInvariant : ∀ generator cell →
  Orbit.orbitClass (act generator cell) ≡ Orbit.orbitClass cell
orbitClassGeneratorInvariant generator cell =
  trans
    (orbitClassAsCount (act generator cell))
    (trans
      (cong classFromCount (outerCountGeneratorInvariant generator cell))
      (sym (orbitClassAsCount cell)))

------------------------------------------------------------------------
-- Reflexive-transitive generated action.
------------------------------------------------------------------------

data HypercubicPath : Grid.GridCell4 → Grid.GridCell4 → Set where
  pathRefl : ∀ {cell} → HypercubicPath cell cell
  pathStep : ∀ generator cell → HypercubicPath cell (act generator cell)
  pathTrans : ∀ {left middle right} →
    HypercubicPath left middle → HypercubicPath middle right →
    HypercubicPath left right

pathTargetCong :
  ∀ {left middle right} →
  HypercubicPath left middle → middle ≡ right → HypercubicPath left right
pathTargetCong path refl = path

pathSymStep : ∀ generator cell →
  HypercubicPath (act generator cell) cell
pathSymStep generator cell =
  pathTargetCong
    (pathStep generator (act generator cell))
    (generatorInvolutive generator cell)

pathSym : ∀ {left right} →
  HypercubicPath left right → HypercubicPath right left
pathSym pathRefl = pathRefl
pathSym (pathStep generator cell) = pathSymStep generator cell
pathSym (pathTrans first second) =
  pathTrans (pathSym second) (pathSym first)

outerCountPathInvariant : ∀ {left right} →
  HypercubicPath left right → Orbit.outerCount left ≡ Orbit.outerCount right
outerCountPathInvariant pathRefl = refl
outerCountPathInvariant (pathStep generator cell) =
  sym (outerCountGeneratorInvariant generator cell)
outerCountPathInvariant (pathTrans first second) =
  trans (outerCountPathInvariant first) (outerCountPathInvariant second)

------------------------------------------------------------------------
-- Constructive canonicalization path.
------------------------------------------------------------------------

positiveFromOuterFlag : Bool → Grid.IntervalCell
positiveFromOuterFlag false = Grid.positiveInner
positiveFromOuterFlag true = Grid.positiveOuter

signNormalize : Grid.GridCell4 → Grid.GridCell4
signNormalize cell =
  Grid.gridCell4
    (positiveFromOuterFlag (Orbit.outerFlag (Grid.c0 cell)))
    (positiveFromOuterFlag (Orbit.outerFlag (Grid.c1 cell)))
    (positiveFromOuterFlag (Orbit.outerFlag (Grid.c2 cell)))
    (positiveFromOuterFlag (Orbit.outerFlag (Grid.c3 cell)))

normalize0 : Grid.GridCell4 → Grid.GridCell4
normalize0 cell =
  Grid.gridCell4
    (positiveFromOuterFlag (Orbit.outerFlag (Grid.c0 cell)))
    (Grid.c1 cell) (Grid.c2 cell) (Grid.c3 cell)

normalize1 : Grid.GridCell4 → Grid.GridCell4
normalize1 cell =
  Grid.gridCell4 (Grid.c0 cell)
    (positiveFromOuterFlag (Orbit.outerFlag (Grid.c1 cell)))
    (Grid.c2 cell) (Grid.c3 cell)

normalize2 : Grid.GridCell4 → Grid.GridCell4
normalize2 cell =
  Grid.gridCell4 (Grid.c0 cell) (Grid.c1 cell)
    (positiveFromOuterFlag (Orbit.outerFlag (Grid.c2 cell)))
    (Grid.c3 cell)

normalize3 : Grid.GridCell4 → Grid.GridCell4
normalize3 cell =
  Grid.gridCell4 (Grid.c0 cell) (Grid.c1 cell) (Grid.c2 cell)
    (positiveFromOuterFlag (Orbit.outerFlag (Grid.c3 cell)))

normalize0Path : ∀ cell → HypercubicPath cell (normalize0 cell)
normalize0Path (Grid.gridCell4 Grid.negativeOuter b c d) = pathStep flip0 _
normalize0Path (Grid.gridCell4 Grid.negativeInner b c d) = pathStep flip0 _
normalize0Path (Grid.gridCell4 Grid.positiveInner b c d) = pathRefl
normalize0Path (Grid.gridCell4 Grid.positiveOuter b c d) = pathRefl

normalize1Path : ∀ cell → HypercubicPath cell (normalize1 cell)
normalize1Path (Grid.gridCell4 a Grid.negativeOuter c d) = pathStep flip1 _
normalize1Path (Grid.gridCell4 a Grid.negativeInner c d) = pathStep flip1 _
normalize1Path (Grid.gridCell4 a Grid.positiveInner c d) = pathRefl
normalize1Path (Grid.gridCell4 a Grid.positiveOuter c d) = pathRefl

normalize2Path : ∀ cell → HypercubicPath cell (normalize2 cell)
normalize2Path (Grid.gridCell4 a b Grid.negativeOuter d) = pathStep flip2 _
normalize2Path (Grid.gridCell4 a b Grid.negativeInner d) = pathStep flip2 _
normalize2Path (Grid.gridCell4 a b Grid.positiveInner d) = pathRefl
normalize2Path (Grid.gridCell4 a b Grid.positiveOuter d) = pathRefl

normalize3Path : ∀ cell → HypercubicPath cell (normalize3 cell)
normalize3Path (Grid.gridCell4 a b c Grid.negativeOuter) = pathStep flip3 _
normalize3Path (Grid.gridCell4 a b c Grid.negativeInner) = pathStep flip3 _
normalize3Path (Grid.gridCell4 a b c Grid.positiveInner) = pathRefl
normalize3Path (Grid.gridCell4 a b c Grid.positiveOuter) = pathRefl

normalize01 : Grid.GridCell4 → Grid.GridCell4
normalize01 cell = normalize1 (normalize0 cell)

normalize012 : Grid.GridCell4 → Grid.GridCell4
normalize012 cell = normalize2 (normalize01 cell)

signNormalizePath : ∀ cell → HypercubicPath cell (signNormalize cell)
signNormalizePath cell =
  pathTrans (normalize0Path cell)
    (pathTrans
      (normalize1Path (normalize0 cell))
      (pathTrans
        (normalize2Path (normalize01 cell))
        (normalize3Path (normalize012 cell))))

shouldSwap : Grid.IntervalCell → Grid.IntervalCell → Bool
shouldSwap left right with Orbit.outerFlag left | Orbit.outerFlag right
... | false | true = true
... | _ | _ = false

sort01 : Grid.GridCell4 → Grid.GridCell4
sort01 cell with shouldSwap (Grid.c0 cell) (Grid.c1 cell)
... | true = act swap01 cell
... | false = cell

sort12 : Grid.GridCell4 → Grid.GridCell4
sort12 cell with shouldSwap (Grid.c1 cell) (Grid.c2 cell)
... | true = act swap12 cell
... | false = cell

sort23 : Grid.GridCell4 → Grid.GridCell4
sort23 cell with shouldSwap (Grid.c2 cell) (Grid.c3 cell)
... | true = act swap23 cell
... | false = cell

sort01Path : ∀ cell → HypercubicPath cell (sort01 cell)
sort01Path cell with shouldSwap (Grid.c0 cell) (Grid.c1 cell)
... | true = pathStep swap01 cell
... | false = pathRefl

sort12Path : ∀ cell → HypercubicPath cell (sort12 cell)
sort12Path cell with shouldSwap (Grid.c1 cell) (Grid.c2 cell)
... | true = pathStep swap12 cell
... | false = pathRefl

sort23Path : ∀ cell → HypercubicPath cell (sort23 cell)
sort23Path cell with shouldSwap (Grid.c2 cell) (Grid.c3 cell)
... | true = pathStep swap23 cell
... | false = pathRefl

-- Bubble network for four Boolean outer flags, moving `outer=true` left.
sortPass1a sortPass1b sortPass1
  sortPass2a sortPass2 sortOuterAxes : Grid.GridCell4 → Grid.GridCell4
sortPass1a = sort23
sortPass1b cell = sort12 (sortPass1a cell)
sortPass1 cell = sort01 (sortPass1b cell)
sortPass2a cell = sort23 (sortPass1 cell)
sortPass2 cell = sort12 (sortPass2a cell)
sortOuterAxes cell = sort23 (sortPass2 cell)

sortOuterAxesPath : ∀ cell → HypercubicPath cell (sortOuterAxes cell)
sortOuterAxesPath cell =
  pathTrans (sort23Path cell)
    (pathTrans (sort12Path (sortPass1a cell))
      (pathTrans (sort01Path (sortPass1b cell))
        (pathTrans (sort23Path (sortPass1 cell))
          (pathTrans (sort12Path (sortPass2a cell))
            (sort23Path (sortPass2 cell))))))

representative : Orbit.OrbitClass → Grid.GridCell4
representative Orbit.infrared =
  Grid.gridCell4 Grid.positiveInner Grid.positiveInner
    Grid.positiveInner Grid.positiveInner
representative Orbit.oneOuter = Orbit.oneOuterRepresentative
representative Orbit.twoOuter = Orbit.twoOuterRepresentative
representative Orbit.threeOuter = Orbit.threeOuterRepresentative
representative Orbit.fourOuter = Orbit.fourOuterRepresentative

sortedNormalizedIsRepresentative : ∀ cell →
  sortOuterAxes (signNormalize cell)
  ≡ representative (Orbit.orbitClass cell)
sortedNormalizedIsRepresentative cell
  with Orbit.outerFlag (Grid.c0 cell)
     | Orbit.outerFlag (Grid.c1 cell)
     | Orbit.outerFlag (Grid.c2 cell)
     | Orbit.outerFlag (Grid.c3 cell)
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

cellPathToOrbitRepresentative : ∀ cell →
  HypercubicPath cell (representative (Orbit.orbitClass cell))
cellPathToOrbitRepresentative cell =
  pathTrans
    (signNormalizePath cell)
    (pathTargetCong
      (sortOuterAxesPath (signNormalize cell))
      (sortedNormalizedIsRepresentative cell))

------------------------------------------------------------------------
-- Physical-scalar consequence: generator invariance is enough. There is no
-- separate "same-orbit values agree" authority field.
------------------------------------------------------------------------

record GeneratorInvariantRationalContribution
    (contribution : Grid.GridCell4 → ℚ) : Set where
  field
    generatorInvariant : ∀ generator cell →
      contribution cell ≡ contribution (act generator cell)
open GeneratorInvariantRationalContribution public

pathRationalInvariant :
  ∀ {contribution}
    (invariant : GeneratorInvariantRationalContribution contribution)
    {left right} → HypercubicPath left right →
  contribution left ≡ contribution right
pathRationalInvariant invariant pathRefl = refl
pathRationalInvariant invariant (pathStep generator cell) =
  generatorInvariant invariant generator cell
pathRationalInvariant invariant (pathTrans first second) =
  trans (pathRationalInvariant invariant first)
        (pathRationalInvariant invariant second)

cellContributionEqualsOrbitRepresentative :
  ∀ {contribution}
    (invariant : GeneratorInvariantRationalContribution contribution)
    cell →
  contribution cell
  ≡ contribution (representative (Orbit.orbitClass cell))
cellContributionEqualsOrbitRepresentative invariant cell =
  pathRationalInvariant invariant (cellPathToOrbitRepresentative cell)

hypercubicGeneratedActionLevel : ProofLevel
hypercubicGeneratedActionLevel = machineChecked

hypercubicOrbitTransitivityOnGeneratedGridLevel : ProofLevel
hypercubicOrbitTransitivityOnGeneratedGridLevel = machineChecked

-- Remaining physical leaf: prove the fully reduced Wilson/ghost/Haar scalar
-- contribution is invariant under these seven concrete generators. Once that
-- is done, four representative values (or, more robustly, four joint orbit
-- sums) exhaust the 240 regular boxes.
literalOneLoopGeneratorInvarianceLevel : ProofLevel
literalOneLoopGeneratorInvarianceLevel = conditional
