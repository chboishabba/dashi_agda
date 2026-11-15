module DASHI.Moonshine.Y443Nonary72EquivarianceNoGoExact where

------------------------------------------------------------------------
-- MAX-CUT: The graph-canonical 72-block is NOT equivariantly identical
-- to the naive reduced-nonary-8 x mode-phase-9 chart under their NATURAL
-- involutions.
--
-- Source graph Y443 swaps the two long arms but fixes a central-square
-- relator IN the selected 72-block. On the existing reduced nonary eight,
-- phase inversion flips the Orientation2 coordinate and fixes NO point.
-- Therefore the product 8x9 chart has no fixed point when inversion acts
-- on its 8-factor, irrespective of the 9-factor.
--
-- This is a mathematically decisive falsifier of the naive commuting
-- square, not a no-go for alternative charts or C3/Fricke identifications.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443ArmSwapOrbitMaxCutExact as Orbit
import DASHI.Moonshine.Y443Relator72IndexedBidiExact as Index
import DASHI.Foundations.Base369MonsterNamedIdentityRegistryExact as Registry
import DASHI.Foundations.Base369FiveModePhaseQuotientExact as Five

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl eq = eq

------------------------------------------------------------------------
-- Canonical unordered-pair normalization prevents the graph automorphism
-- from leaving the actual 66-pair Y443 index list. The old raw
-- pair(x,y)->pair(swap x,swap y) was NOT closed on that enumeration.
------------------------------------------------------------------------

rank : Y.Node → Nat
rank Y.a = 0
rank Y.b1 = 1
rank Y.c1 = 2
rank Y.d1 = 3
rank Y.e1 = 4
rank Y.b2 = 5
rank Y.c2 = 6
rank Y.d2 = 7
rank Y.e2 = 8
rank Y.b3 = 9
rank Y.c3 = 10
rank Y.d3 = 11

leq : Nat → Nat → Bool
leq zero _ = true
leq (suc _) zero = false
leq (suc x) (suc y) = leq x y

canonicalPair : Y.Node → Y.Node → Y.Pair
canonicalPair x y with leq (rank x) (rank y)
... | true = Y.pair x y
... | false = Y.pair y x

swapTag : Index.RelatorTag → Index.RelatorTag
swapTag (Index.nodeSquare n) = Index.nodeSquare (Orbit.swap n)
swapTag (Index.pairPower (Y.pair x y)) =
  Index.pairPower (canonicalPair (Orbit.swap x) (Orbit.swap y))
swapTag Index.spider = Index.spider
swapTag Index.centralQuotient = Index.centralQuotient

-- This is a literal proof over the ACTUAL 66 unordered-pair indices.
-- It fails definitionally if the canonical pair sort is wrong.
allListedPairsReturnAfterDoubleSwap :
  Y.map (λ p → swapTag (swapTag (Index.pairPower p))) Y.pairs
  ≡ Y.map Index.pairPower Y.pairs
allListedPairsReturnAfterDoubleSwap = refl

swapNodeInvolutive :
  (n : Y.Node) →
  swapTag (swapTag (Index.nodeSquare n)) ≡ Index.nodeSquare n
swapNodeInvolutive n rewrite Orbit.swapInvolutive n = refl

-- Exhaustive 12x12 *relator-role* equivariance; this does not assert
-- literal word equality of the spider or central quotient under swap.
coreSwapInvariant : (tag : Index.RelatorTag) →
  Index.core (swapTag tag) ≡ Index.core tag
coreSwapInvariant (Index.nodeSquare Y.a) = refl
coreSwapInvariant (Index.nodeSquare Y.b1) = refl
coreSwapInvariant (Index.nodeSquare Y.c1) = refl
coreSwapInvariant (Index.nodeSquare Y.d1) = refl
coreSwapInvariant (Index.nodeSquare Y.e1) = refl
coreSwapInvariant (Index.nodeSquare Y.b2) = refl
coreSwapInvariant (Index.nodeSquare Y.c2) = refl
coreSwapInvariant (Index.nodeSquare Y.d2) = refl
coreSwapInvariant (Index.nodeSquare Y.e2) = refl
coreSwapInvariant (Index.nodeSquare Y.b3) = refl
coreSwapInvariant (Index.nodeSquare Y.c3) = refl
coreSwapInvariant (Index.nodeSquare Y.d3) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.a Y.a)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.a Y.b1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.a Y.c1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.a Y.d1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.a Y.e1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.a Y.b2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.a Y.c2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.a Y.d2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.a Y.e2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.a Y.b3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.a Y.c3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.a Y.d3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b1 Y.a)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b1 Y.b1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b1 Y.c1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b1 Y.d1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b1 Y.e1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b1 Y.b2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b1 Y.c2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b1 Y.d2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b1 Y.e2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b1 Y.b3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b1 Y.c3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b1 Y.d3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c1 Y.a)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c1 Y.b1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c1 Y.c1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c1 Y.d1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c1 Y.e1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c1 Y.b2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c1 Y.c2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c1 Y.d2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c1 Y.e2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c1 Y.b3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c1 Y.c3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c1 Y.d3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d1 Y.a)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d1 Y.b1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d1 Y.c1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d1 Y.d1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d1 Y.e1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d1 Y.b2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d1 Y.c2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d1 Y.d2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d1 Y.e2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d1 Y.b3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d1 Y.c3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d1 Y.d3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e1 Y.a)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e1 Y.b1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e1 Y.c1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e1 Y.d1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e1 Y.e1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e1 Y.b2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e1 Y.c2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e1 Y.d2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e1 Y.e2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e1 Y.b3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e1 Y.c3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e1 Y.d3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b2 Y.a)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b2 Y.b1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b2 Y.c1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b2 Y.d1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b2 Y.e1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b2 Y.b2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b2 Y.c2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b2 Y.d2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b2 Y.e2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b2 Y.b3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b2 Y.c3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b2 Y.d3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c2 Y.a)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c2 Y.b1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c2 Y.c1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c2 Y.d1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c2 Y.e1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c2 Y.b2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c2 Y.c2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c2 Y.d2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c2 Y.e2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c2 Y.b3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c2 Y.c3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c2 Y.d3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d2 Y.a)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d2 Y.b1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d2 Y.c1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d2 Y.d1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d2 Y.e1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d2 Y.b2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d2 Y.c2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d2 Y.d2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d2 Y.e2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d2 Y.b3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d2 Y.c3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d2 Y.d3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e2 Y.a)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e2 Y.b1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e2 Y.c1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e2 Y.d1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e2 Y.e1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e2 Y.b2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e2 Y.c2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e2 Y.d2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e2 Y.e2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e2 Y.b3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e2 Y.c3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.e2 Y.d3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b3 Y.a)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b3 Y.b1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b3 Y.c1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b3 Y.d1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b3 Y.e1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b3 Y.b2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b3 Y.c2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b3 Y.d2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b3 Y.e2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b3 Y.b3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b3 Y.c3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.b3 Y.d3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c3 Y.a)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c3 Y.b1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c3 Y.c1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c3 Y.d1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c3 Y.e1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c3 Y.b2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c3 Y.c2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c3 Y.d2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c3 Y.e2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c3 Y.b3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c3 Y.c3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.c3 Y.d3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d3 Y.a)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d3 Y.b1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d3 Y.c1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d3 Y.d1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d3 Y.e1)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d3 Y.b2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d3 Y.c2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d3 Y.d2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d3 Y.e2)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d3 Y.b3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d3 Y.c3)) = refl
coreSwapInvariant (Index.pairPower (Y.pair Y.d3 Y.d3)) = refl
coreSwapInvariant Index.spider = refl
coreSwapInvariant Index.centralQuotient = refl

record CoreTag : Set where
  constructor coreTag
  field
    tag : Index.RelatorTag
    isCore : Index.core tag ≡ true

open CoreTag public

swapCore : CoreTag → CoreTag
swapCore (coreTag source proof) =
  coreTag (swapTag source) (trans (coreSwapInvariant source) proof)

centralCore : CoreTag
centralCore = coreTag (Index.nodeSquare Y.a) refl

centralCoreFixed : swapCore centralCore ≡ centralCore
centralCoreFixed = refl

------------------------------------------------------------------------
-- Use the actual existing reduced-nonary-eight, not a new fake Fin 8.
------------------------------------------------------------------------

flipReducedNonary8 : Registry.ReducedNonary8 → Registry.ReducedNonary8
flipReducedNonary8 (mode , Five.negativeOrientation) =
  mode , Five.positiveOrientation
flipReducedNonary8 (mode , Five.positiveOrientation) =
  mode , Five.negativeOrientation

reducedEightHasNoFixedPoint :
  (state : Registry.ReducedNonary8) →
  flipReducedNonary8 state ≡ state → ⊥
reducedEightHasNoFixedPoint (mode , Five.negativeOrientation) ()
reducedEightHasNoFixedPoint (mode , Five.positiveOrientation) ()

flipMode9 : Five.ModePhaseQuotient9 → Five.ModePhaseQuotient9
flipMode9 Five.identityMode = Five.identityMode
flipMode9 Five.A2negative = Five.A2positive
flipMode9 Five.A2positive = Five.A2negative
flipMode9 Five.B1negative = Five.B1positive
flipMode9 Five.B1positive = Five.B1negative
flipMode9 Five.B2negative = Five.B2positive
flipMode9 Five.B2positive = Five.B2negative
flipMode9 Five.Enegative = Five.Epositive
flipMode9 Five.Epositive = Five.Enegative

Chart72 : Set
Chart72 = Registry.ReducedNonary8 × Five.ModePhaseQuotient9

flipChart : Chart72 → Chart72
flipChart (r , m) = flipReducedNonary8 r , flipMode9 m

chartHasNoFixedPoint :
  (state : Chart72) → flipChart state ≡ state → ⊥
chartHasNoFixedPoint state eq =
  reducedEightHasNoFixedPoint (proj₁ state) (cong proj₁ eq)

record EquivariantChart : Set where
  field
    toChart : CoreTag → Chart72
    commutesWithFlip :
      (tag : CoreTag) →
      toChart (swapCore tag) ≡ flipChart (toChart tag)

open EquivariantChart public

-- No even one-way equivariant map exists under these selected actions.
noNaiveEightByNineEquivariantChart : EquivariantChart → ⊥
noNaiveEightByNineEquivariantChart chart =
  chartHasNoFixedPoint
    (toChart chart centralCore)
    (trans
      (sym (cong (toChart chart) centralCoreFixed))
      (commutesWithFlip chart centralCore))
