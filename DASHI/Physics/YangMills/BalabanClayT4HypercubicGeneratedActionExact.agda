module DASHI.Physics.YangMills.BalabanClayT4HypercubicGeneratedActionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Hermann Weyl, "The Classical Groups: Their Invariants and
-- Representations", Princeton University Press, 2nd ed. (1946). No DOI.
-- Kenneth G. Wilson, "Confinement of Quarks", Phys. Rev. D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445.
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I.", Commun. Math. Phys. 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
-- Construct the signed-coordinate flips and adjacent axis transpositions on
-- the actual generated 4^4 Brillouin grid.  These seven involutions generate
-- the hyperoctahedral action.  We prove outer-degree invariance and construct
-- a path from every cell to the canonical representative of its degree by
-- sign normalization followed by a six-comparator Boolean sorting network.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
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

flipIntervalInvolutive : ∀ c → flipInterval (flipInterval c) ≡ c
flipIntervalInvolutive Grid.negativeOuter = refl
flipIntervalInvolutive Grid.negativeInner = refl
flipIntervalInvolutive Grid.positiveInner = refl
flipIntervalInvolutive Grid.positiveOuter = refl

outerWeightFlipInvariant : ∀ c →
  Orbit.outerWeight (flipInterval c) ≡ Orbit.outerWeight c
outerWeightFlipInvariant Grid.negativeOuter = refl
outerWeightFlipInvariant Grid.negativeInner = refl
outerWeightFlipInvariant Grid.positiveInner = refl
outerWeightFlipInvariant Grid.positiveOuter = refl

data HypercubicGenerator : Set where
  flip0 flip1 flip2 flip3 swap01 swap12 swap23 : HypercubicGenerator

act : HypercubicGenerator → Grid.GridCell4 → Grid.GridCell4
act flip0 (Grid.gridCell4 a b c d) = Grid.gridCell4 (flipInterval a) b c d
act flip1 (Grid.gridCell4 a b c d) = Grid.gridCell4 a (flipInterval b) c d
act flip2 (Grid.gridCell4 a b c d) = Grid.gridCell4 a b (flipInterval c) d
act flip3 (Grid.gridCell4 a b c d) = Grid.gridCell4 a b c (flipInterval d)
act swap01 (Grid.gridCell4 a b c d) = Grid.gridCell4 b a c d
act swap12 (Grid.gridCell4 a b c d) = Grid.gridCell4 a c b d
act swap23 (Grid.gridCell4 a b c d) = Grid.gridCell4 a b d c

generatorInvolutive : ∀ g cell → act g (act g cell) ≡ cell
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

-- (a+b)+c = (a+c)+b: the only arithmetic move needed for adjacent swaps.
swapAdjacentAfterPrefix : ∀ a b c → (a + b) + c ≡ (a + c) + b
swapAdjacentAfterPrefix a b c =
  trans (+-assoc a b c)
    (trans (cong (a +_) (+-comm b c)) (sym (+-assoc a c b)))

outerCountGeneratorInvariant : ∀ g cell →
  Orbit.outerCount (act g cell) ≡ Orbit.outerCount cell
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
  cong (_+ Orbit.outerWeight d)
    (sym (swapAdjacentAfterPrefix
      (Orbit.outerWeight a) (Orbit.outerWeight b) (Orbit.outerWeight c)))
outerCountGeneratorInvariant swap23 (Grid.gridCell4 a b c d) =
  sym (swapAdjacentAfterPrefix
    (Orbit.outerWeight a + Orbit.outerWeight b)
    (Orbit.outerWeight c) (Orbit.outerWeight d))

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

orbitClassGeneratorInvariant : ∀ g cell →
  Orbit.orbitClass (act g cell) ≡ Orbit.orbitClass cell
orbitClassGeneratorInvariant g cell =
  trans (orbitClassAsCount (act g cell))
    (trans (cong classFromCount (outerCountGeneratorInvariant g cell))
      (sym (orbitClassAsCount cell)))

data HypercubicPath : Grid.GridCell4 → Grid.GridCell4 → Set where
  pathRefl : ∀ {cell} → HypercubicPath cell cell
  pathStep : ∀ g cell → HypercubicPath cell (act g cell)
  pathTrans : ∀ {a b c} →
    HypercubicPath a b → HypercubicPath b c → HypercubicPath a c

pathTargetCong : ∀ {a b c} →
  HypercubicPath a b → b ≡ c → HypercubicPath a c
pathTargetCong path refl = path

pathSym : ∀ {a b} → HypercubicPath a b → HypercubicPath b a
pathSym pathRefl = pathRefl
pathSym (pathStep g cell) =
  pathTargetCong (pathStep g (act g cell)) (generatorInvolutive g cell)
pathSym (pathTrans first second) = pathTrans (pathSym second) (pathSym first)

positiveFromOuterFlag : Bool → Grid.IntervalCell
positiveFromOuterFlag false = Grid.positiveInner
positiveFromOuterFlag true = Grid.positiveOuter

normalize0 normalize1 normalize2 normalize3 : Grid.GridCell4 → Grid.GridCell4
normalize0 (Grid.gridCell4 a b c d) =
  Grid.gridCell4 (positiveFromOuterFlag (Orbit.outerFlag a)) b c d
normalize1 (Grid.gridCell4 a b c d) =
  Grid.gridCell4 a (positiveFromOuterFlag (Orbit.outerFlag b)) c d
normalize2 (Grid.gridCell4 a b c d) =
  Grid.gridCell4 a b (positiveFromOuterFlag (Orbit.outerFlag c)) d
normalize3 (Grid.gridCell4 a b c d) =
  Grid.gridCell4 a b c (positiveFromOuterFlag (Orbit.outerFlag d))

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

normalize01 normalize012 signNormalize : Grid.GridCell4 → Grid.GridCell4
normalize01 cell = normalize1 (normalize0 cell)
normalize012 cell = normalize2 (normalize01 cell)
signNormalize cell = normalize3 (normalize012 cell)

signNormalizePath : ∀ cell → HypercubicPath cell (signNormalize cell)
signNormalizePath cell =
  pathTrans (normalize0Path cell)
    (pathTrans (normalize1Path (normalize0 cell))
      (pathTrans (normalize2Path (normalize01 cell))
        (normalize3Path (normalize012 cell))))

shouldSwap : Grid.IntervalCell → Grid.IntervalCell → Bool
shouldSwap left right with Orbit.outerFlag left | Orbit.outerFlag right
... | false | true = true
... | _ | _ = false

sort01 sort12 sort23 : Grid.GridCell4 → Grid.GridCell4
sort01 cell with shouldSwap (Grid.c0 cell) (Grid.c1 cell)
... | true = act swap01 cell
... | false = cell
sort12 cell with shouldSwap (Grid.c1 cell) (Grid.c2 cell)
... | true = act swap12 cell
... | false = cell
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

p1a p1b p1 p2a p2 sortOuterAxes : Grid.GridCell4 → Grid.GridCell4
p1a = sort23
p1b cell = sort12 (p1a cell)
p1 cell = sort01 (p1b cell)
p2a cell = sort23 (p1 cell)
p2 cell = sort12 (p2a cell)
sortOuterAxes cell = sort23 (p2 cell)

sortOuterAxesPath : ∀ cell → HypercubicPath cell (sortOuterAxes cell)
sortOuterAxesPath cell =
  pathTrans (sort23Path cell)
    (pathTrans (sort12Path (p1a cell))
      (pathTrans (sort01Path (p1b cell))
        (pathTrans (sort23Path (p1 cell))
          (pathTrans (sort12Path (p2a cell)) (sort23Path (p2 cell))))))

representative : Orbit.OrbitClass → Grid.GridCell4
representative Orbit.infrared =
  Grid.gridCell4 Grid.positiveInner Grid.positiveInner Grid.positiveInner Grid.positiveInner
representative Orbit.oneOuter = Orbit.oneOuterRepresentative
representative Orbit.twoOuter = Orbit.twoOuterRepresentative
representative Orbit.threeOuter = Orbit.threeOuterRepresentative
representative Orbit.fourOuter = Orbit.fourOuterRepresentative

sortedNormalizedIsRepresentative : ∀ cell →
  sortOuterAxes (signNormalize cell) ≡ representative (Orbit.orbitClass cell)
sortedNormalizedIsRepresentative (Grid.gridCell4 a b c d)
  with Orbit.outerFlag a | Orbit.outerFlag b | Orbit.outerFlag c | Orbit.outerFlag d
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
  pathTrans (signNormalizePath cell)
    (pathTargetCong (sortOuterAxesPath (signNormalize cell))
      (sortedNormalizedIsRepresentative cell))

record GeneratorInvariantRationalContribution
    (contribution : Grid.GridCell4 → ℚ) : Set where
  field
    generatorInvariant : ∀ g cell → contribution cell ≡ contribution (act g cell)
open GeneratorInvariantRationalContribution public

pathRationalInvariant : ∀ {f}
  (invariant : GeneratorInvariantRationalContribution f) {a b} →
  HypercubicPath a b → f a ≡ f b
pathRationalInvariant invariant pathRefl = refl
pathRationalInvariant invariant (pathStep g cell) =
  generatorInvariant invariant g cell
pathRationalInvariant invariant (pathTrans first second) =
  trans (pathRationalInvariant invariant first) (pathRationalInvariant invariant second)

cellContributionEqualsOrbitRepresentative : ∀ {f}
  (invariant : GeneratorInvariantRationalContribution f) cell →
  f cell ≡ f (representative (Orbit.orbitClass cell))
cellContributionEqualsOrbitRepresentative invariant cell =
  pathRationalInvariant invariant (cellPathToOrbitRepresentative cell)

hypercubicGeneratedActionLevel : ProofLevel
hypercubicGeneratedActionLevel = machineChecked
hypercubicOrbitTransitivityOnGeneratedGridLevel : ProofLevel
hypercubicOrbitTransitivityOnGeneratedGridLevel = machineChecked

-- Physical leaf: prove the reduced Wilson/ghost/Haar scalar contribution is
-- invariant under these seven concrete generators.
literalOneLoopGeneratorInvarianceLevel : ProofLevel
literalOneLoopGeneratorInvarianceLevel = conditional
